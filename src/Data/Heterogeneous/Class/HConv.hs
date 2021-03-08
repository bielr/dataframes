{-# language UndecidableInstances #-}
module Data.Heterogeneous.Class.HConv where

import GHC.Exts (Any)

import Control.Lens (view)

import qualified Data.Primitive.SmallArray as SA

import Unsafe.Coerce (unsafeCoerce)

import Data.Heterogeneous.RIxed
import Data.Heterogeneous.RNew


-- Conversion between record types

type HConv :: forall k. HTyConK k -> HTyConK k -> Constraint

class HConv hf hg as where
    hconv :: hf f as -> hg f as


instance KnownLength as => HConv HList HSmallArray as where
    hconv = HSA.unsafeFromListN getSNat . toAnys
      where
        toAnys :: HList f as -> [Any]
        toAnys HNil      = []
        toAnys (a :& as) = unsafeCoerce a : toAnys as
    {-# inline hconv #-}


instance {-# overlappable #-} HConv hf hf as where
    hconv = id
    {-# inline hconv #-}

instance {-# overlappable #-} (HIxed hf, HNew HList as) => HConv hf HList as where
    hconv hf = rcreate (\i -> view (hix i) hf)
    {-# inline hconv #-}
