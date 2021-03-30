{-# language AllowAmbiguousTypes #-}
{-# language GADTs #-}
{-# language StrictData #-}
{-# language TypeSynonymInstances #-}
{-# language QuantifiedConstraints #-}
{-# language UndecidableInstances #-}
{-# language ViewPatterns #-}
module Data.Frame.Dplyr.Basic where

import Prelude hiding (drop, filter, zipWith)

import Control.Lens qualified as L
import Control.Lens.LazyTraversal qualified as L
import Control.Lens.Type
import Control.Lens.Indexed (Indexable)

import Data.Vector.Generic qualified as VG

import Data.Frame.Column
import Data.Frame.Dplyr.Ops
import Data.Frame.Field
import Data.Frame.Frame
import Data.Frame.Internal.Column
import Data.Frame.Internal.Frame
import Data.Frame.Internal.Repr
import Data.Frame.Types
import Data.Indexer
import Data.Vinyl.Extra qualified as VE


cat :: a -> a
cat = id
{-# inline cat #-}


(!@) :: forall rec cols rep by.
    When (by == 'Cols)
        ( RFunctor rec
        , When (rep == 'Vec) (ColTypes cols)
        )
    => Frame rep by rec cols
    -> Indexer Int
    -> Frame 'Idx by rec cols
df !@ idx =
    case df of
      ByRows -> df
          & indexFrame
          & frameRows %~ (`backpermuteIndexer` idx)
      ByCols -> df
          & colsLength .~ length idx
          & rmapCols \c -> c
              & indexCol
              & colRepF %~ (`backpermuteIndexer` idx)
{-# inline (!@) #-}


col :: forall i s a b col col' cols cols' rec rep colF by f p.
    ( FieldSpec cols i col
    , col ~ '(s, a)
    , col' ~ '(s, b)
    , RReplace rec col col' cols cols'
    , When (by == 'Rows)
        ( colF ~ Field
        , Indexable Int p
        , Applicative f
        , When (rep == 'Idx) (L.DistributiveFoldable f)
        )
    , When (by == 'Cols)
        ( colF ~ Col rep
        , p ~ (->)
        , Functor f
        )
    )
    => Over p f
        (Frame rep by rec cols) (Frame rep by rec cols')
        (colF col)              (colF col')
col pafb df =
    case df of
      RowsVec rows ->
          RowsVec <$> L.conjoined (traverse . VE.rlens) (L.itraversed <. VE.rlens) pafb rows
      RowsGen rows ->
          RowsGen <$> L.conjoined (L.foldMapped . VE.rlens) (L.ifoldMapped <. VE.rlens) pafb rows
      ByCols ->
          (colsRec . VE.rlens) pafb df
{-# inline col #-}


cols :: forall i subs subs' cols cols' rec rep.
    ( FieldSpec cols i subs
    , RSubseq rec subs subs' cols cols'
    , KnownRepr rep
    )
    => Lens
        (Frame rep 'Cols rec cols) (Frame rep 'Cols rec cols')
        (Frame rep 'Cols rec subs) (Frame rep 'Cols rec subs')
cols f df = df
    & colsRec . VE.rsubseq . asFrameOfLength (df^.colsLength) %%~ f
{-# inline cols #-}


get :: forall i s a col cols rec by rep.
    ( FieldSpec cols i col
    , col ~ '(s, a)
    , RElem rec col cols
    , When (by == 'Cols && rep == 'Vec) (ColType col)
    , Forbid (by == 'Rows && rep == 'Idx)
        "Individually accessing multiple columns of a row\
        \ indexer is inefficient, use vals instead"
    )
    => ColIx (Frame rep by rec cols) a
get = ColIx \df ->
    case df of
      ByCols       -> colIx $ VE.rget @col $ view frameCols df
      RowsVec rows -> getField . VE.rget @col . elemAt (indexVector rows)
      RowsGen rows -> getField . VE.rget @col . elemAt rows
{-# inline get #-}


getRow_ ::
    VE.RTupled rec cols
    => ColIx (Frame rep 'Rows rec cols) (VE.RTupleHKDOf Field cols)
getRow_ = ColIx \df ->
    case df of
      RowsVec rows -> VE.rtupleHKD . elemAt (indexVector rows)
      RowsGen rows -> VE.rtupleHKD . elemAt rows
{-# inline getRow_ #-}


getRow :: forall i cols rec rep.
    ( FieldSpec cols i cols -- better make them explicit to avoid bugs
    , VE.RTupled rec cols
    )
    => ColIx (Frame rep 'Rows rec cols) (VE.RTupleHKDOf Field cols)
getRow = getRow_
{-# inline getRow #-}


into :: forall is colnames cols rec.
    ( NameSpec is colnames
    , RTupled rec cols
    , "to do"
    )
    => RTupleHKDOf Field cols

into = undefined


singleCol :: forall col col' rep colRep rep' by rec rec'.
    ( When (by == 'Rows) (colRep ~ 'Idx)
    , When (by == 'Cols) (colRep ~ rep)
    , When (rep' == 'Vec) (ColType col')
    , VE.RSingleton rec
    , VE.RSingleton rec'
    )
    => Iso
        (Frame rep by rec '[col]) (Frame rep' 'Cols rec' '[col'])
        (Col colRep col)          (Col rep' col')
singleCol = L.iso deframe enframe
  where
    deframe :: Frame rep by rec '[col] -> Col colRep col
    deframe df =
        case df of
          ByCols -> df ^. frameCols . VE.rsingleton
          ByRows -> ColGen $ indexFrame df ^. frameRows . L.mapping VE.rsingleton

    enframe :: Col rep' col' -> Frame rep' 'Cols rec' '[col']
    enframe c =
        case c of
          ColGen g -> ColGens (length g)    (VE.rsingleton # c)
          ColVec v -> ColVecs (VG.length v) (VE.rsingleton # c)


{-
only :: forall i s a b rec. (NameSpec i s, RSingleton rec)
     => Iso (Row rec '[ '(s, a)]) (Row rec '[ '(s, b)]) a b
only = rsingleton . elfield
{-# inline only #-}


singleField :: forall i s a rec. (NameSpec i s, KnownSymbol s, RSingleton rec)
            => a
            -> Fields rec '[ '(s, a)]
singleField = L.review (only @i)
{-# inline singleField #-}


singleRow :: row -> Frame row
singleRow row = Frame { frameLength = 1, frameRow = const row }
{-# inline singleRow #-}


frameProductWith :: (row1 -> row2 -> row3) -> Frame row1 -> Frame row2 -> Frame row3
frameProductWith f df1 df2 = Frame
    { frameLength = n1 * n2
    , frameRow = \i -> f (frameRow df1 (i `div` n2)) (frameRow df2 (i `mod` n2))
    }
  where
    !n1 = frameLength df1
    !n2 = frameLength df2
{-# inline frameProductWith #-}


firstN :: Int -> Frame row -> Frame row
firstN n df = df { frameLength = min (frameLength df) n }
{-# inline firstN #-}


drop :: forall i ss rs q rec.
     ( FieldSpec rs i ss
     , RecQuotient rec ss rs q
     , RMonoid rec
     )
     => FrameFields rec rs
     -> FrameFields rec q
drop = fmap (rquotient @ss)
{-# inline drop #-}


select :: forall is ss rs rec.
       ( FieldSpec rs is ss
       , FieldSubset rec ss rs
       )
       => FrameFields rec rs
       -> FrameFields rec ss
select = fmap V.rcast
{-# inline select #-}


select_ :: forall ss rs rec. FieldSubset rec ss rs
        => FrameFields rec rs
        -> FrameFields rec ss
select_ = fmap V.rcast
{-# inline select_ #-}


mutate :: RMonoid rec
       => (Fields rec cols -> Fields rec new)
       -> FrameFields rec cols
       -> FrameFields rec (new ++ cols)
mutate f = fmap (\row -> rappend (f row) row)
{-# inline mutate #-}


mutate1 :: forall i s a cols rec.
        ( NameSpec i s
        , KnownSymbol s
        , RMonoid rec
        , RSingleton rec
        )
        => (Fields rec cols -> a)
        -> FrameFields rec cols
        -> FrameFields rec ('(s, a) ': cols)
mutate1 f = fmap (\row -> rcons (V.Field (f row)) row)
{-# inline mutate1 #-}


replace :: forall i s a b col col' cols cols' rec.
        ( FieldSpec cols i col
        , col ~ '(s, a)
        , col' ~ '(s, b)
        , ReplField rec col col' cols cols'
        )
       => (Fields rec cols -> b)
       -> FrameFields rec cols
       -> FrameFields rec cols'
replace f = rows %~ \row -> L.set (field @col) (f row) row
{-# inline replace #-}


filter :: (row -> Bool) -> Frame row -> Frame row
filter f = rowsVec %~ Vec.filter f
{-# inline filter #-}


dropNothings :: forall i s a col col' cols cols' rec.
             ( FieldSpec cols i col
             , KnownSymbol s
             , col ~ '(s, Maybe a)
             , col' ~ '(s, a)
             , GetField rec col cols
             , ReplField rec col col' cols cols'
             )
             => FrameFields rec cols
             -> FrameFields rec cols'
dropNothings = rowsVec %~ Vec.mapMaybe (L.sequenceAOf (field @col))
{-# inline dropNothings #-}


unnest :: forall i s a col col' cols cols' rec.
       ( FieldSpec cols i col
       , col ~ '(s, [a])
       , col' ~ '(s, a)
       , ReplField rec col col' cols cols'
       )
       => FrameFields rec cols
       -> FrameFields rec cols'
unnest =
    rowsVec %~ Vec.concatMap (Vec.fromList . L.sequenceAOf (field @col))
{-# inline unnest #-}


unnestFrame :: forall i s col col's cols cols' rec.
            ( FieldSpec cols i col
            , col ~ '(s, FrameFields rec col's)
            , GetField rec col cols
            , ReplFields rec '[col] col's cols cols'
            , RSingleton rec
            )
            => FrameFields rec cols
            -> FrameFields rec cols'
unnestFrame =
    rowsVec %~ Vec.concatMap (toRowsVec . factorFrameOut)
  where
    factorFrameOut :: Fields rec cols -> FrameFields rec cols'
    factorFrameOut = L.traverseOf (rsubseq @col) (V.getField . view rsingleton)
{-# inline unnestFrame #-}


rename :: forall i i' s s' a col col' cols cols' rec.
        ( FieldSpec cols i col
        , NameSpec i' s'
        , col ~ '(s, a)
        , col' ~ '(s', a)
        , KnownSymbol s'
        , ReplField rec col col' cols cols'
        )
        => FrameFields rec cols
        -> FrameFields rec cols'
rename = fmap (rrename @i @i')
{-# inline rename #-}


reorder :: EquivFields rec rs rs' => FrameFields rec rs -> FrameFields rec rs'
reorder = fmap V.rcast
{-# inline reorder #-}

-}
