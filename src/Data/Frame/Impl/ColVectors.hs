--{-# options_ghc -ddump-simpl -dsuppress-idinfo -dsuppress-unfoldings -dsuppress-coercions #-}
{-# language ApplicativeDo #-}
{-# language RoleAnnotations #-}
{-# language MagicHash #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language TemplateHaskell #-}
{-# language UndecidableInstances #-}
module Data.Frame.Impl.ColVectors where

import GHC.Stack

import Control.Lens hiding ((:>))
import Control.Rowwise
import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Lens (vectorTraverse)

import Data.Frame.Class
import Data.Frame.DataTypes.Vector
import Data.Frame.Kind
import Data.Frame.TypeIndex
import Data.Heterogeneous.Class.HMonoid
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.Class.Subseq
import Data.Heterogeneous.HSmallArray (HSmallArray)
import Data.Heterogeneous.HTuple
import Data.Heterogeneous.TypeLevel


type Column :: FieldK -> Type
newtype Column col = Column (Vector (FieldType col))


type Columns :: FieldsK -> Type
type Columns cols = HSmallArray Column cols


type Frame :: FrameK
data Frame cols = Frame
    { _nrow :: !Int
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


    col :: forall col cols i proxy.
        ( FieldSpecProxy col cols i proxy
        , KnownField Frame col
        , HGet HSmallArray col cols
        )
        => proxy
        -> Env Frame cols (FieldType col)
    col _ =
        FrameEnv $ unsafeRowwise \(Frame _ cols) ->
            let Column v = hget @col cols
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


newCol :: forall s a cols proxy.
    ( NameSpecProxy s proxy
    , KnownDataType Frame a
    )
    => proxy
    -> Frame cols
    -> Env Frame cols a
    -> Column (s :> a)
newCol _ df@(Frame n _) (FrameEnv rww) =
    Column (VG.generate n (runRowwise rww df))


prependCol :: forall s a cols proxy.
    ( NameSpecProxy s proxy
    , KnownDataType Frame a
    )
    => proxy
    -> Env Frame cols a
    -> Frame cols
    -> Frame ((s :> a) ': cols)
prependCol proxy env df@(Frame n cols) =
    Frame n (newCol proxy df env `hcons` cols)


appendCol :: forall s a cols proxy.
    ( NameSpecProxy s proxy
    , KnownDataType Frame a
    )
    => proxy
    -> Env Frame cols a
    -> Frame cols
    -> Frame (cols ++ '[s :> a])
appendCol proxy env df@(Frame n cols) =
    Frame n (cols `hsnoc` newCol proxy df env)


restricting :: forall cols1' cols2' cols1 cols2 is proxy.
    ( FieldSpecProxy cols1' cols1 is proxy
    , HSubseq HSmallArray cols1' cols2' cols1 cols2
    )
    => proxy
    -> Lens (Frame cols1) (Frame cols2) (Frame cols1') (Frame cols2')
restricting _ f df@(Frame n _) =
    (columns . hsubseq @cols1' @cols2' . frameOfLength n) f df


transmute :: forall cols' ss' cols t proxy.
    ( NameSpecProxy ss' proxy
    , cols' ~ ZipWith (:>) ss' (TupleMembers t)
    )
    => proxy
    -> Env Frame cols t
    -> Frame cols
    -> Frame cols'
transmute = undefined

-- materializeCol :: forall s a cols. Rowwise (Frame cols) a -> Column (s :> a)
-- materializeCol = undefined
