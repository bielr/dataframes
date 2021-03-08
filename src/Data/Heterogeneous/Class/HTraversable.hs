module Data.Heterogeneous.Class.HTraversable where

import Data.Heterogeneous.Functors
import Data.Heterogeneous.Class.HFoldable
import Data.Heterogeneous.Class.HFunctor
import Data.Heterogeneous.TypeLevel


-- Traversable-like records

type HTraversable :: forall k. HTyConK k -> Constraint

class (HFunctor hf, HFoldable hf) => HTraversable hf where
    htraverse ::
        Applicative g
        => (forall a. f a -> g (h a))
        -> hf f as
        -> g (hf h as)

    htraverse2 ::
        Applicative g
        => (forall a. f a -> f' a -> g (h a))
        -> hf f as
        -> hf f' as
        -> g (hf h as)


hsequence :: (HTraversable hf, Applicative g) => hf (g :. f) as -> g (hf f as)
hsequence = htraverse getCompose
{-# inline hsequence #-}

