--{-# options_ghc -ddump-simpl -dsuppress-idinfo -dsuppress-unfoldings -dsuppress-coercions #-}
{-# language ApplicativeDo #-}
{-# language AllowAmbiguousTypes #-}
{-# language RoleAnnotations #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedLabels #-}
{-# language TemplateHaskell #-}
{-# language UndecidableInstances #-}
module Data.Frame.Impl.ColVectors where

import GHC.OverloadedLabels
import Control.Lens (Iso, coerced)
import Control.Rowwise
import Data.Vector.Generic qualified as VG

import Data.Frame.Kind
import Data.Frame.Class
import Data.Frame.TH.Expr (rowwise)
import Data.Frame.DataTypes.Vector
import Data.Frame.TypeIndex
import Data.Heterogeneous.HSmallArray (HSmallArray)
import Data.Heterogeneous.Class.HMonoid
import Data.Heterogeneous.Class.Member


type Column :: FieldK -> Type
newtype Column col = Column (Vector (FieldType col))


colVector :: Iso (Column (s :> a)) (Column (s :> b)) (Vector a) (Vector b)
colVector = coerced


type Frame :: FrameK
data Frame cols = Frame !Int !(HSmallArray Column cols)


class (VG.Vector Vector a, KnownVectorMode (VectorModeOf a)) => KnownDataType_ a
instance (VG.Vector Vector a, KnownVectorMode (VectorModeOf a)) => KnownDataType_ a


instance IsFrame Frame HSmallArray where
    type KnownDataType Frame = KnownDataType_

    -- type Env :: FieldsK -> Type -> Type -> Type
    -- type role Env nominal nominal nominal representational
    newtype Env Frame cols tok a = FrameEnv (Rowwise (Frame cols) a)
        deriving newtype (Functor, Applicative)

    getCol (_ :: proxy col) =
        FrameEnv $ unsafeRowwise \(Frame _ cols) ->
            let Column v = hget @col cols
                !i       = VG.unsafeIndex v
            in i


instance
    ( a ~ FindFieldType s cols
    , KnownDataType Frame a
    , HGet HSmallArray (FindField s cols) cols
    )
    => IsLabel s (Env Frame cols tok a) where
    fromLabel =
        FrameEnv $ unsafeRowwise \(Frame _ cols) ->
            let Column v = hget @(FindField s cols) cols
                !i        = VG.unsafeIndex v
            in i


test :: Env Frame '["a":>Int, "b":>Char, "c":>Double] tok Double
test = do
    a <- col @"a"
    c <- col @"c"
    pure (fromIntegral a + c)


test2 :: Env Frame '["a":>Int, "b":>Char, "c":>Double] tok Double
test2 = $(rowwise [| fromIntegral #a + #c |])
--       [rowwise| fromIntegral #a + #c*#a |]


newCol :: forall s a cols.
    KnownDataType Frame a
    => Frame cols
    -> (forall tok. Env Frame cols tok a) -> Column (s :> a)
newCol df@(Frame nrow _) env =
    case env @() of
        FrameEnv rww ->
            Column (VG.generate nrow (runRowwise rww df))


testAppend ::
    Frame '["a":>Int, "b":>Char, "c":>Double]
    -> Frame '["a":>Int, "b":>Char, "c":>Double, "d":>Double]
testAppend df@(Frame nrow cols) =
    let d = newCol df test
    in  Frame nrow (hsnoc cols d)


materializeCol :: forall s a cols. Rowwise (Frame cols) a -> Column (s :> a)
materializeCol = undefined
