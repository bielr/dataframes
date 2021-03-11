{-# language UndecidableInstances #-}
module Data.Heterogeneous.Class.HConv where

import Control.Lens (view)

import Data.Heterogeneous.TypeLevel.Kind
import Data.Heterogeneous.Class.HCreate
import Data.Heterogeneous.Class.Member


-- Conversion between record types

type HConv :: forall {k}. HTyConK k -> HTyConK k -> [k] -> Constraint

class HConv hf hg as where
    hconv :: hf f as -> hg f as

    default hconv :: (HIxed hf, HCreate hg as) => hf f as -> hg f as
    hconv hf = hcreate \i -> view (hix i) hf


hconvTo :: forall hg hf f as. HConv hf hg as => hf f as -> hg f as
hconvTo = hconv

instance {-# overlappable #-} HConv hf hf as where
    hconv = id
    {-# inline hconv #-}
