--{-# options_ghc -ddump-simpl -dsuppress-idinfo -dsuppress-unfoldings -dsuppress-coercions #-}
{-# language ApplicativeDo #-}
{-# language RoleAnnotations #-}
{-# language MagicHash #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language TemplateHaskell #-}
{-# language UndecidableInstances #-}
module Data.Frame.Impl.ColVectors where

import Prelude hiding ((.))

import GHC.Exts (IsList)
import GHC.Stack

import Control.Category (Category(..))
import Control.Lens hiding ((:>))
import Control.Monad
import Control.Monad.ST qualified as ST
import Control.Rowwise
import Data.Coerce
import Data.Type.Coercion
import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Lens (vectorTraverse)
import Data.Vector.Generic.Mutable qualified as VGM

import Data.Frame.Class
import Data.Frame.DataTypes.Vector
import Data.Frame.Field
import Data.Frame.Kind
import Data.Frame.TypeIndex
import Data.Indexer
import Data.Heterogeneous.Class.HCoerce
import Data.Heterogeneous.Class.HCreate
import Data.Heterogeneous.Class.HMonoid
import Data.Heterogeneous.Class.HFoldable
import Data.Heterogeneous.Class.HTraversable
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.Class.Subseq
import Data.Heterogeneous.Class.TupleView
import Data.Heterogeneous.Constraints
import Data.Heterogeneous.HSmallArray (HSmallArray)
import Data.Heterogeneous.HTuple
import Data.Heterogeneous.TypeLevel


type MutableColumn :: Type -> FieldK -> Type
newtype MutableColumn s col = MutableColumn (MVector s (FieldType col))


type Columns :: FieldsK -> Type
type Columns cols = HSmallArray (Column Frame) cols


type MutableColumns :: Type -> FieldsK -> Type
type MutableColumns s cols = HSmallArray (MutableColumn s) cols


type Frame :: FrameK
data Frame cols = Frame
    { _nrow    :: !Int
    , _columns :: !(Columns cols)
    }

makeLenses ''Frame


class (VG.Vector Vector a, KnownVectorMode (VectorModeOf a)) => KnownDataType_ a
instance (VG.Vector Vector a, KnownVectorMode (VectorModeOf a)) => KnownDataType_ a


colVector :: Iso (Column Frame (s :> a)) (Column Frame (s :> b)) (Vector a) (Vector b)
colVector = coerced


colValues ::
    ( KnownDataType Frame a
    , KnownDataType Frame b
    )
    => IndexedTraversal Int (Column Frame (s :> a)) (Column Frame (s :> b)) a b
colValues = colVector.vectorTraverse


instance IsFrame Frame where
    type KnownDataType Frame = KnownDataType_

    frameLength (Frame n _) = n

    type Record Frame = HSmallArray

    newtype instance Column Frame col = Column (Vector (FieldType col))

    colFields = colVector.asIndexer

    -- type Env :: FieldsK -> Type -> Type -> Type
    -- type role Env nominal nominal nominal representational
    newtype Env Frame cols a = FrameEnv (Rowwise (Frame cols) a)
        deriving newtype (Functor, Applicative)

    runEnv df@(Frame n _) (FrameEnv rww) = Indexer n $! runRowwise rww df


deriving newtype instance IsList (Vector (FieldType col)) => IsList (Column Frame col)


instance (KnownField Frame col, HGetI HSmallArray col cols i) => GetCol Frame col cols i where
    getCol _ =
        FrameEnv $ unsafeRowwise \(Frame _ cols) ->
            let Column v = hgetI @_ @_ @_ @i cols
                !i       = VG.unsafeIndex v
            in i


instance Columnar Frame HSmallArray cols where
    unsafeFromColsLength = Frame
    toCols (Frame _ cols) = cols




checkLengths :: HasCallStack => Int -> Int -> Int
checkLengths !n !m
  | n == m    = n
  | otherwise = error $
        "data frame length mismatch: " ++ show n ++ " /= " ++ show m
{-# inline checkLengths #-}


-- this ensures that the user does not modify the length of the frame
-- throws error if not preserved!
frameOfLength :: forall cols cols'.
    HasCallStack
    => Int
    -> Iso
        (Columns cols) (Columns cols')
        (Frame cols)   (Frame cols')
frameOfLength n =
    iso (Frame n) deframe
  where
    deframe :: Frame cols' -> Columns cols'
    deframe (Frame m cs) = checkLengths n m `seq` cs
{-# inline frameOfLength #-}



newCol ::
    KnownField Frame col
    => Frame cols
    -> Env Frame cols (Field col)
    -> Column Frame col
newCol df@(Frame n _) (FrameEnv rww) =
    Column (VG.generate n (coerce (runRowwise rww df)))


prependCol ::
    KnownField Frame col
    => Env Frame cols (Field col)
    -> Frame cols
    -> Frame (col ': cols)
prependCol env df@(Frame n cols) =
    Frame n (newCol df env `hcons` cols)


appendCol ::
    KnownField Frame col
    => Env Frame cols (Field col)
    -> Frame cols
    -> Frame (cols ++ '[col])
appendCol env df@(Frame n cols) =
    Frame n (cols `hsnoc` newCol df env)


restricting :: forall is cols1' cols2' cols1 cols2 proxy.
    ( IsFieldsProxy cols1 is proxy
    , HSubseqI HSmallArray cols1' cols2' cols1 cols2 is
    )
    => proxy
    -> Lens (Frame cols1) (Frame cols2) (Frame cols1') (Frame cols2')
restricting _ f df@(Frame n _) =
    (columns . hsubseqI @_ @cols1' @cols2' @cols1 @cols2 @is . frameOfLength n) f df



type FieldWriter :: Type -> FieldK -> Type
newtype FieldWriter s col = FieldWriter
    { runSTWriter :: Int -> FieldType col -> ST.ST s ()
    }


-- fromCols :: forall cols t cs.
--     ( TupleView HSmallArray cols
--     , IsTupleOf cs t
--     , Mapped Column cols cs
--     , HCoerce HTuple cols
--     , All (KnownField Frame) cols
--     )
--     => t
--     -> Maybe (Frame cols)
-- fromCols colsTup =
--     let colsArr :: HSmallArray Column cols
--         colsArr = fromHTuple $ coerceWith (hIdLCo . hconOutCo . htupleCo) colsTup
--
--         lengths :: HSmallArray Column cols -> [Int]
--         lengths = hitoListWith $
--             constrained @(KnownField Frame) @cols \(Column v) -> VG.length v
--     in
--         case lengths colsArr of
--             []     -> Just (Frame 0 colsArr)
--             (l:ls)
--               | all (==l) ls -> Just (Frame l colsArr)
--               | otherwise    -> Nothing


transmute :: forall cols' cols t.
    ( KnownLength cols'

    , HCoerce HTuple cols'
    , HTraversable HTuple cols'
    , TupleView HSmallArray cols'

    , IsTupleOf (TupleMembers t) t
    , Mapped Field cols' (TupleMembers t)

    , All (KnownField Frame) cols'
    )
    => Env Frame cols t
    -> Frame cols
    -> Frame cols'
transmute (FrameEnv rww) df@(Frame n _) = ST.runST do
    let tupleGen :: Int -> t
        !tupleGen = runRowwise rww df

        fieldCo :: t :~>: HTuple Field cols'
        !fieldCo = hIdLCo . hconOutCo . htupleCo

        fieldsGen :: Int -> HTuple Field cols'
        !fieldsGen = gcoerceWith fieldCo (coerce tupleGen)

    mcols' <- initMVs

    let writers = toWriters mcols'

    forM_ [0..n-1] \i ->
        htraverse2_ (\w (Field a) -> runSTWriter w i a)
            writers
            (fieldsGen i)

    cols' <- freezeCols mcols'

    return (Frame n cols')
  where
    initMVs :: ST.ST s (HSmallArray (MutableColumn s) cols')
    initMVs =
        hcreateA $
            constrained @(KnownField Frame) @cols' $
                MutableColumn <$> VGM.unsafeNew n

    freezeCols ::
        HSmallArray (MutableColumn s) cols'
        -> ST.ST s (HSmallArray (Column Frame) cols')
    freezeCols =
        hitraverse $
            constrained @(KnownField Frame) @cols' \(MutableColumn mv) ->
                Column <$> VG.unsafeFreeze mv

    toWriters ::
        HSmallArray (MutableColumn s) cols'
        -> HTuple (FieldWriter s) cols'
    toWriters =
        htupleWithC @_ @_ @(KnownField Frame) \(MutableColumn mv) ->
            FieldWriter (VGM.unsafeWrite mv)

