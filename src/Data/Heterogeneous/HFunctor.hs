-- {-# options_ghc -ddump-simpl -dsuppress-idinfo -dsuppress-unfoldings -dsuppress-coercions #-}
{-# language AllowAmbiguousTypes #-}
module Data.Heterogeneous.HFunctor
  ( HFunctor(..)
  , rimapC
  , rmapC
  , rmap21
  , rmap12
  , rmap22
  ) where

import Data.Heterogeneous.Functors

import Data.Heterogeneous.Constraints
import Data.Heterogeneous.TypeLevel


type HFunctor :: forall k. HTyCon k -> Constraint

class HFunctor hf where
    hmap ::
        (forall x. f x -> g x)
        -> hf f as
        -> hf g as
    hmap f = himap \_ -> f

    hzipWith ::
        (forall x. f x -> g x -> h x)
        -> hf f as
        -> hf g as
        -> hf h as
    hzipWith f = hizipWith \_ -> f

    himap ::
        (forall i. i < Length as => SNat i -> f (as !! i) -> g (as !! i))
        -> hf f as
        -> hf g as

    hizipWith ::
        (forall i. i < Length as => SNat i -> f (as !! i) -> g (as !! i) -> h (as !! i))
        -> hf f as
        -> hf g as
        -> hf h as


rimapC :: forall c as hf f g.
    (All c as, HFunctor hf)
    => (forall i. (i < Length as, c (as !! i)) => SNat i -> f (as !! i) -> g (as !! i))
    -> hf f as
    -> hf g as
rimapC h = himap (iconstrained @c @as h)
{-# inline rimapC #-}


rmapC :: forall c as hf f g.
    (All c as, HFunctor hf)
    => (forall x. c x => f x -> g x)
    -> hf f as
    -> hf g as
rmapC h = himap (constrained @c @as h)
{-# inline rmapC #-}


rmap21 :: HFunctor hf => (forall x. f (g x) -> h x) -> hf (f :. g) as -> hf h as
rmap21 h = hmap \(Compose fgx) -> h fgx
{-# inline rmap21 #-}


rmap12 :: HFunctor hf => (forall x. f x -> g (h x)) -> hf f as -> hf (g :. h) as
rmap12 h = hmap \fx -> Compose (h fx)
{-# inline rmap12 #-}


rmap22 :: HFunctor hf => (forall x. f (g x) -> f' (g' x)) -> hf (f :. g) as -> hf (f' :. g') as
rmap22 h = hmap \(Compose fgx) -> Compose (h fgx)
{-# inline rmap22 #-}
