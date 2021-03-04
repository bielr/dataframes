{-# language AllowAmbiguousTypes #-}
{-# language QuantifiedConstraints #-}
{-# language UndecidableInstances #-}
module Data.Frame.Dplyr.Group where

import qualified Control.Foldl as Foldl
import qualified Control.Lens as L
import Control.Lens.Type

import Data.Bifunctor (second)
import Data.Foldable (toList)
import Data.Function (on)
import Data.Kind (Constraint, Type)
import Data.Map.Strict (Map)
import Data.Monoid (Ap(..))
import qualified Data.Vector                as Vec
import qualified Data.Vector.Unboxed        as UVec
import qualified Data.Vector.Algorithms.Tim as Tim

import Data.Vinyl qualified as Vy

import Data.Frame.Dplyr.Basic
import Data.Frame.Field
import Data.Frame.Types
import Data.Vinyl.Extra qualified as VE


type AsKey :: RecK -> FieldsK -> Constraint

class AsKey rec keys where
    type KeyType :: RecK -> (FieldsK -> Type) -> FieldsK -> Type
    type KeyType rec f keys = t | t -> f keys

    type HasKey :: RecK -> FieldsK -> FieldsK -> Constraint
    type HasKey rec keys cols

    rkey :: HasKey keys rec cols => Lens' (rec f cols) (KeyType rec f keys)
    keyRecord :: Iso' (KeyType rec f keys) (rec f keys)


instance AsKey '[col] where
    type KeyType rec f '[col] = f col

    type HasKey rec '[col] cols = RElem rec col cols

    rkey = VE.rlens
    keyRecord = VE.rsingleton


instance AsKey (col1 ': col2 ': cols) where
    type KeyType rec f (col1 ': col2 ': cols) = rec f (col1 ': col2 ': cols)

    type HasKey rec (col1 ': col2 ': cols) colss = RSubset rec (col1 ': col2 ': cols) colss

    rkey = VE.rsubset
    keyRecord = id


data GroupingMethod assoc rec keys = GroupingMethod
    { groupBy :: forall rep by cols.
          ( HasKey rec keys cols
          , When (by == 'Cols && rep == 'Vec) (ColTypes cols)
          )
          => Frame rep by rec cols
          -> assoc (KeyType rec Field keys) (Frame rep by rec cols)

    , splitGroups ::
          assoc (KeyType rec Field keys) (Frame rep by rec cols)
          -> [(KeyType rec Field keys, Frame rep by rec cols)]
    }


type GroupingKey rec keys cols =
    ( AsKey keys
    , Ord (KeyType keys rec)
    , HasKey keys rec cols
    , KeyRecordCtx keys rec
    )


data SortOrder = forall i. Asc i | forall i. Desc i

class SortKey rec i cols where
    compareRows :: Fields rec cols -> Fields rec cols -> Ordering

instance (FieldSpec cols i keys, GroupingKey rec keys cols) => SortKey rec (Asc i) cols where
    compareRows = compare `on` getKey @keys

instance (FieldSpec cols i keys, GroupingKey rec keys cols) => SortKey rec (Desc i) cols where
    compareRows = flip (compareRows @rec @(Asc i))

instance SortKey rec ('[] :: [SortOrder]) cols where
    compareRows _ _ = EQ

instance (SortKey rec i cols, SortKey rec is cols) => SortKey rec (i ': is :: [SortOrder]) cols where
    compareRows row1 row2 =
        compareRows @rec @i row1 row2 <> compareRows @rec @is row1 row2


arrangeBy :: (row -> row -> Ordering) -> Frame row -> Frame row
arrangeBy cmp df =
    df !@ reorderedIdxs
  where
    cmp' :: Int -> Int -> Ordering
    cmp' i j = cmp (frameRow df i) (frameRow df j)

    nrows :: Int
    nrows = frameLength df

    reorderedIdxs :: UVec.Vector Int
    reorderedIdxs = UVec.modify (Tim.sortBy cmp') (UVec.generate nrows id)
{-# inline arrangeBy #-}


arrange :: forall is cols rec. SortKey rec is cols => FrameFields rec cols -> FrameFields rec cols
arrange = arrangeBy (compareRows @rec @is)
{-# inline arrange #-}


topBy :: (row -> row -> Ordering) -> Int -> Frame row -> Frame row
topBy cmp n = firstN n . arrangeBy cmp
{-# inline topBy #-}


top :: forall is cols rec. SortKey rec is cols => Int -> FrameFields rec cols -> FrameFields rec cols
top = topBy (compareRows @rec @is)
{-# inline top #-}


splitSortOn :: forall k row row'. Ord k => (row -> (k, row')) -> Frame row -> [(k, Frame row')]
splitSortOn key =
    let
      cacheKeys :: Frame row -> Frame (k, row')
      cacheKeys = fmap key

      arrangedRows :: Frame (k, row') -> Vec.Vector (k, row')
      arrangedRows = toRowsVec . arrangeBy (\(k1, _) (k2, _) -> compare k1 k2)

      splitVec :: Vec.Vector (k, row') -> [(k, Vec.Vector (k, row'))]
      splitVec v
        | Vec.null v = []
        | otherwise  =
            let
              (currentKey, _) = Vec.head v
              (group, rest) = Vec.span (\(k, _) -> k == currentKey) v
            in
              (currentKey, group) : splitVec rest
    in
      map (second $ fmap snd . fromRowsVec) . splitVec . arrangedRows . cacheKeys
{-# inlinable splitSortOn #-}


splitOn :: forall k row. Ord k => (row -> k) -> Frame row -> [Frame row]
splitOn key df =
    let buildSubframes :: Map k [Int] -> [Frame row]
        buildSubframes = map (df !@) . toList . fmap UVec.fromList

        grouper :: Foldl.Fold Int [Frame row]
        grouper = buildSubframes <$> Foldl.groupBy (key . frameRow df) Foldl.list
    in
        Foldl.fold grouper df { frameRow = id }
{-# inlinable splitOn #-}


groupedOn :: forall k row row'. Ord k
          => (row -> k)
          -> IndexedTraversal k
               (Frame row) (Frame row')
               (Frame row) (Frame row')
groupedOn key f =
    getAp . foldMap (Ap . uncurry (L.indexed f)) . splitSortOn (\row -> (key row, row))
{-# inline groupedOn #-}


-- NOTE: not a lawful traversal because it sorts the frame
grouped :: forall i keys cols cols' rec rec'.
        ( FieldSpec cols i keys
        , GroupingKey rec keys cols
        )
        => IndexedTraversal (KeyType keys rec)
             (FrameFields rec cols) (FrameFields rec' cols')
             (FrameFields rec cols) (FrameFields rec' cols')
grouped = groupedOn (getKey @keys)
{-# inline grouped #-}


-- NOTE: not a lawful traversal because it sorts the frame
fixed :: forall i keys cols cols' rec rec'.
       ( FieldSpec cols i keys
       , GroupingKey rec keys cols
       , KeyRecordCtx keys rec'
       , KeyType keys rec ~ KeyType keys rec'
       , RMonoid rec'
       )
       => IndexedTraversal (KeyType keys rec)
            (FrameFields rec cols) (FrameFields rec' (keys ++ cols'))
            (FrameFields rec cols) (FrameFields rec' cols')
fixed f =
    grouped @i $ L.Indexed $ \k ->
        let !recKey = L.view (keyRecord @keys) k
            !f'     = ixf k
        in  \group -> fmap (rowwise (rappend recKey)) (f' group)
  where
    ixf = L.indexed f
{-# inline fixed #-}


-- NOTE: not a lawful traversal because it sorts the frame
summarizing :: forall i keys cols cols' rec rec'.
            ( FieldSpec cols i keys
            , GroupingKey rec keys cols
            , KeyRecordCtx keys rec'
            , KeyType keys rec ~ KeyType keys rec'
            , RMonoid rec'
            )
            => IndexedTraversal (KeyType keys rec)
                 (FrameFields rec cols) (FrameFields rec' (keys ++ cols'))
                 (FrameFields rec cols) (Fields rec' cols')
summarizing = fixed @i . L.rmap (fmap singleRow)
{-# inline summarizing #-}
