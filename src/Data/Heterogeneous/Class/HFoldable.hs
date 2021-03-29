-- {-# options_ghc -ddump-simpl -dsuppress-idinfo -dsuppress-unfoldings -dsuppress-coercions #-}
module Data.Heterogeneous.Class.HFoldable where

import Data.Heterogeneous.TypeLevel


type HFoldable :: forall {k}. HTyConK k -> [k] -> Constraint

class HFoldable hf as where
    hfoldr :: forall r f.
        (forall a. f a -> r -> r)
        -> r
        -> hf f as
        -> r
    hfoldr f = hifoldr \_ -> f

    hfoldr2 :: forall r f g.
        (forall a. f a -> g a -> r -> r)
        -> r
        -> hf f as
        -> hf g as
        -> r
    hfoldr2 f = hifoldr2 \_ -> f

    hifoldr :: forall r f.
        (forall i. i < Length as => SNat i -> f (as !! i) -> r -> r)
        -> r
        -> hf f as
        -> r

    hifoldr2 :: forall r f g.
        (forall i. i < Length as => SNat i -> f (as !! i) -> g (as !! i) -> r -> r)
        -> r
        -> hf f as
        -> hf g as
        -> r


    hfoldl' :: forall r f.
        (forall a. r -> f a -> r)
        -> r
        -> hf f as
        -> r
    hfoldl' f z0 hf = hfoldr f' id hf z0
      where
        f' :: f a -> (r -> r) -> r -> r
        f' fa k z = k $! f z fa


    hifoldl' :: forall r f.
        (forall i. i < Length as => r -> SNat i -> f (as !! i) -> r)
        -> r
        -> hf f as
        -> r
    hifoldl' f z0 hf = hifoldr f' id hf z0
      where
        f' :: i < Length as => SNat i -> f (as !! i) -> (r -> r) -> r -> r
        f' i fa k z = k $! f z i fa


    hfoldl2' :: forall r f g.
        (forall a. r -> f a -> g a -> r)
        -> r
        -> hf f as
        -> hf g as
        -> r
    hfoldl2' f z0 hf hg = hfoldr2 f' id hf hg z0
      where
        f' :: f a -> g a -> (r -> r) -> r -> r
        f' fa ga k z = k $! f z fa ga


    hifoldl2' :: forall r f g.
        (forall i. i < Length as => r -> SNat i -> f (as !! i) -> g (as !! i) -> r)
        -> r
        -> hf f as
        -> hf g as
        -> r
    hifoldl2' f z0 hf hg = hifoldr2 f' id hf hg z0
      where
        f' :: i < Length as => SNat i -> f (as !! i) -> g (as !! i) -> (r -> r) -> r -> r
        f' i fa ga k z = k $! f z i fa ga


htoListWith ::
    HFoldable hf as
    => (forall a. f a -> b)
    -> hf f as
    -> [b]
htoListWith f = hfoldr (\fa r -> f fa : r) []
{-# inline htoListWith #-}


hitoListWith ::
    HFoldable hf as
    => (forall i. i < Length as => SNat i -> f (as !! i) -> b)
    -> hf f as
    -> [b]
hitoListWith f = hifoldr (\i fa r -> f i fa : r) []
{-# inline hitoListWith #-}


htraverse_ ::
    (HFoldable hf as, Applicative g)
    => (forall a. f a -> g ())
    -> hf f as
    -> g ()
htraverse_ f = hfoldr (\fa r -> f fa *> r) (pure ())
{-# inline htraverse_ #-}


htraverse2_ ::
    (HFoldable hf as, Applicative h)
    => (forall a. f a -> g a -> h ())
    -> hf f as
    -> hf g as
    -> h ()
htraverse2_ f = hfoldr2 (\fa ga r -> f fa ga *> r) (pure ())
{-# inline htraverse2_ #-}


hitraverse_ ::
    (HFoldable hf as, Applicative g)
    => (forall i. i < Length as => SNat i -> f (as !! i) -> g ())
    -> hf f as
    -> g ()
hitraverse_ f = hifoldr (\i fa r -> f i fa *> r) (pure ())
{-# inline hitraverse_ #-}


hitraverse2_ ::
    (HFoldable hf as, Applicative h)
    => (forall i. i < Length as => SNat i -> f (as !! i) -> g (as !! i) -> h ())
    -> hf f as
    -> hf g as
    -> h ()
hitraverse2_ f = hifoldr2 (\i fa ga r -> f i fa ga *> r) (pure ())
{-# inline hitraverse2_ #-}
