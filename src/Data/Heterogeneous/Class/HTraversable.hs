module Data.Heterogeneous.Class.HTraversable where

import Data.Heterogeneous.Functors
import Data.Heterogeneous.Class.HFoldable
import Data.Heterogeneous.Class.HFunctor
import Data.Heterogeneous.TypeLevel


-- Traversable-like records

type HTraversable :: forall k. HTyConK k -> [k] -> Constraint

class (HFunctor hf as, HFoldable hf as) => HTraversable hf as where
    htraverse ::
        Applicative g
        => (forall a. f a -> g (h a))
        -> hf f as
        -> g (hf h as)
    htraverse f = hitraverse \_ a -> f a

    hitraverse ::
        Applicative g
        => (forall i. i < Length as => SNat i -> f (as !! i) -> g (h (as !! i)))
        -> hf f as
        -> g (hf h as)

    htraverse2 ::
        Applicative g
        => (forall a. f a -> f' a -> g (h a))
        -> hf f as
        -> hf f' as
        -> g (hf h as)
    htraverse2 f = hitraverse2 \_ a b -> f a b

    hitraverse2 ::
        Applicative g
        => (forall i. i < Length as => SNat i -> f (as !! i) -> f' (as !! i) -> g (h (as !! i)))
        -> hf f as
        -> hf f' as
        -> g (hf h as)

hsequence :: (HTraversable hf as, Applicative g) => hf (g :. f) as -> g (hf f as)
hsequence = htraverse getCompose
{-# inline hsequence #-}

