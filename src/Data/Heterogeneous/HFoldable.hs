-- {-# options_ghc -ddump-simpl -dsuppress-idinfo -dsuppress-unfoldings -dsuppress-coercions #-}
module Data.Heterogeneous.HFoldable where

import Data.Heterogeneous.TypeLevel


type HFoldable :: forall k. HTyCon k -> Constraint

class HFoldable rec where
    hfoldr ::
        (forall a. f a -> r -> r)
        -> r
        -> rec f as
        -> r
    hfoldr f = hifoldr \_ -> f

    hfoldr2 ::
        (forall a. f a -> g a -> r -> r)
        -> r
        -> rec f as
        -> rec g as
        -> r
    hfoldr2 f = hifoldr2 \_ -> f

    hifoldr ::
        (forall i. i < Length as => SNat i -> f (as !! i) -> r -> r)
        -> r
        -> rec f as
        -> r

    hifoldr2 ::
        (forall i. i < Length as => SNat i -> f (as !! i) -> g (as !! i) -> r -> r)
        -> r
        -> rec f as
        -> rec g as
        -> r


htraverse_ ::
    (HFoldable rec, Applicative g)
    => (forall a. f a -> g ())
    -> rec f as
    -> g ()
htraverse_ f = hfoldr (\fa r -> f fa *> r) (pure ())
{-# inline htraverse_ #-}


htraverse2_ ::
    (HFoldable rec, Applicative h)
    => (forall a. f a -> g a -> h ())
    -> rec f as
    -> rec g as
    -> h ()
htraverse2_ f = hfoldr2 (\fa ga r -> f fa ga *> r) (pure ())
{-# inline htraverse2_ #-}


hitraverse_ ::
    (HFoldable rec, Applicative g)
    => (forall i. SNat i -> f (as !! i) -> g ())
    -> rec f as
    -> g ()
hitraverse_ f = hifoldr (\i fa r -> f i fa *> r) (pure ())
{-# inline hitraverse_ #-}


hitraverse2_ ::
    (HFoldable rec, Applicative h)
    => (forall i. SNat i -> f (as !! i) -> g (as !! i) -> h ())
    -> rec f as
    -> rec g as
    -> h ()
hitraverse2_ f = hifoldr2 (\i fa ga r -> f i fa ga *> r) (pure ())
{-# inline hitraverse2_ #-}
