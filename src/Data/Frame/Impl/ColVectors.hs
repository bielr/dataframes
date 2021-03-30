--{-# options_ghc -ddump-simpl -dsuppress-idinfo -dsuppress-unfoldings -dsuppress-coercions #-}
{-# language ApplicativeDo #-}
{-# language RoleAnnotations #-}
{-# language MagicHash #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language TemplateHaskell #-}
{-# language UndecidableInstances #-}
module Data.Frame.Impl.ColVectors where

import Prelude hiding ((.))

import GHC.Exts (IsList, proxy#)
import GHC.Stack

import Control.Category (Category(..))
import Control.Lens hiding ((:>))
import Control.Monad
import Control.Monad.ST qualified as ST
import Control.Rowwise
import Data.Type.Coercion
import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Lens (vectorTraverse)
import Data.Vector.Generic.Mutable qualified as VGM

import Data.Frame.Class
import Data.Frame.DataTypes.Vector
import Data.Frame.Field
import Data.Frame.Kind
import Data.Frame.TypeIndex
import Data.Heterogeneous.Class.HCoerce
import Data.Heterogeneous.Class.HCreate
import Data.Heterogeneous.Class.HMonoid
import Data.Heterogeneous.Class.HFoldable
import Data.Heterogeneous.Class.HTraversable
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.Class.Subseq
import Data.Heterogeneous.Class.TupleView
import Data.Heterogeneous.Constraints
import Data.Heterogeneous.Functors
import Data.Heterogeneous.HSmallArray (HSmallArray)
import Data.Heterogeneous.HTuple
import Data.Heterogeneous.TypeLevel
import Type.Errors


type Column :: FieldK -> Type
newtype Column col = Column (Vector (FieldType col))

type MutableColumn :: Type -> FieldK -> Type
newtype MutableColumn s col = MutableColumn (MVector s (FieldType col))

deriving newtype instance IsList (Vector (FieldType col)) => IsList (Column col)


type Columns :: FieldsK -> Type
type Columns cols = HSmallArray Column cols


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


colVector :: Iso (Column (s :> a)) (Column (s :> b)) (Vector a) (Vector b)
colVector = coerced


colValues ::
    (KnownDataType Frame a, KnownDataType Frame b)
    => IndexedTraversal Int (Column (s :> a)) (Column (s :> b)) a b
colValues = colVector.vectorTraverse


instance IsFrame Frame HSmallArray where
    type KnownDataType Frame = KnownDataType_

    -- type Env :: FieldsK -> Type -> Type -> Type
    -- type role Env nominal nominal nominal representational
    newtype Env Frame cols a = FrameEnv (Rowwise (Frame cols) a)
        deriving newtype (Functor, Applicative)


    col :: forall i col cols proxy.
        ( IsFieldsProxy cols i proxy
        , KnownField Frame col
        , HGetI HSmallArray col cols i
        )
        => proxy
        -> Env Frame cols (FieldType col)
    col _ =
        FrameEnv $ unsafeRowwise \(Frame _ cols) ->
            let Column v = hgetI @_ @_ @_ @i cols
                !i       = VG.unsafeIndex v
            in i


checkLengths :: HasCallStack => Int -> Int -> Int
checkLengths !n !m
  | n == m    = n
  | otherwise = error $
        "Frame.checkLength: data frame length mismatch: " ++ show n ++ " /= " ++ show m
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



infixr 0 =.
infixr 0 =..


(=.) :: (IsNameProxy s proxy, Coercible a (f (s :> a))) => proxy -> a -> f (s :> a)
_ =. a = Field a


(=..) :: (IsNameProxy s proxy, Coercible (v a) (f (s :> a))) => proxy -> v a -> f (s :> a)
_ =.. as = Column as


asCol :: IsNameProxy s proxy => proxy -> Vector a -> Column (s :> a)
asCol _ = Column
{-# inline asCol #-}


newCol :: forall s a cols proxy.
    ( IsNameProxy s proxy
    , KnownDataType Frame a
    )
    => proxy
    -> Frame cols
    -> Env Frame cols a
    -> Column (s :> a)
newCol _ df@(Frame n _) (FrameEnv rww) =
    Column (VG.generate n (runRowwise rww df))


prependCol :: forall s a cols proxy.
    ( IsNameProxy s proxy
    , KnownDataType Frame a
    )
    => proxy
    -> Env Frame cols a
    -> Frame cols
    -> Frame ((s :> a) ': cols)
prependCol proxy env df@(Frame n cols) =
    Frame n (newCol proxy df env `hcons` cols)


appendCol :: forall s a cols proxy.
    ( IsNameProxy s proxy
    , KnownDataType Frame a
    )
    => proxy
    -> Env Frame cols a
    -> Frame cols
    -> Frame (cols ++ '[s :> a])
appendCol proxy env df@(Frame n cols) =
    Frame n (cols `hsnoc` newCol proxy df env)


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


fromCols :: forall cols t cs.
    ( TupleView HSmallArray cols
    , IsTupleOf cs t
    , Mapped Column cols cs
    , HCoerce HTuple cols
    , All (KnownField Frame) cols
    )
    => t
    -> Maybe (Frame cols)
fromCols t =
    let cols = fromHTuple (coerceWith (hIdLCo . hconOutCo . htupleCo) t)

        lengths = hitoListWith (constrained @(KnownField Frame) @cols \(Column v) -> VG.length v) cols
    in
        case lengths of
            []     -> Just (Frame 0 cols)
            (l:ls)
              | all (==l) ls -> Just (Frame l cols)
              | otherwise    -> Nothing


transmute :: forall cols' ss' as cols t proxy.
    ( IsNameProxy ss' proxy
    , KnownLength cols'

    , HCoerce HTuple cols'
    , HTraversable HTuple cols'
    , TupleView HSmallArray cols'

    , IsTupleOf as t
    , ZippedFields ss' as cols'

    , All (KnownField Frame) cols'

    , WhenStuck (ForcePeano (Length cols'))
        (DelayError
            ('Text "Could not match names "
                ':<>: 'ShowType ss'
                ':<>: 'Text " with types in "
                ':<>: 'ShowType (TupleMembers t)))
    )
    => proxy
    -> Env Frame cols t
    -> Frame cols
    -> Frame cols'
transmute _ (FrameEnv rww) df@(Frame n _) = ST.runST do
    let tupleGen :: Int -> t
        !tupleGen = runRowwise rww df

        liftCo :: Coercion a b -> Coercion (x -> a) (x -> b)
        liftCo Coercion = Coercion

        htupleGen :: Int -> HTuple Identity (TupleMembers t)
        !htupleGen = coerceWith (liftCo htupleCo) tupleGen

        fieldCo :: NatCoercion Field Identity FieldTypeExp
        !fieldCo = Coercion

        fieldsGen :: Int -> HTuple Field cols'
        !fieldsGen =
            coerceWith
                (sym (liftCo (hliftCoercionF (proxy# @FieldTypeExp) fieldCo)))
                htupleGen

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
        -> ST.ST s (HSmallArray Column cols')
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

