-- {-# options_ghc -ddump-simpl -dsuppress-idinfo -dsuppress-unfoldings -dsuppress-coercions #-}
{-# language AllowAmbiguousTypes #-}
module Data.Heterogeneous.Class.HFunctor
  ( HFunctor(..)
  , himapC
  , hmapC
  , hmap21
  , hmap12
  , hmap22
  ) where

import Data.Heterogeneous.Functors

import Data.Heterogeneous.Constraints
import Data.Heterogeneous.TypeLevel


type HFunctor :: forall k. HTyConK k -> Constraint

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


himapC :: forall c as hf f g.
    (All c as, HFunctor hf)
    => (forall i. (i < Length as, c (as !! i)) => SNat i -> f (as !! i) -> g (as !! i))
    -> hf f as
    -> hf g as
himapC h = himap (iconstrained @c @as h)
{-# inline himapC #-}


hmapC :: forall c as hf f g.
    (All c as, HFunctor hf)
    => (forall x. c x => f x -> g x)
    -> hf f as
    -> hf g as
hmapC h = himap (constrained @c @as h)
{-# inline hmapC #-}


hmap21 :: HFunctor hf => (forall x. f (g x) -> h x) -> hf (f :. g) as -> hf h as
hmap21 h = hmap \(Compose fgx) -> h fgx
{-# inline hmap21 #-}


hmap12 :: HFunctor hf => (forall x. f x -> g (h x)) -> hf f as -> hf (g :. h) as
hmap12 h = hmap \fx -> Compose (h fx)
{-# inline hmap12 #-}


hmap22 :: HFunctor hf => (forall x. f (g x) -> f' (g' x)) -> hf (f :. g) as -> hf (f' :. g') as
hmap22 h = hmap \(Compose fgx) -> Compose (h fgx)
{-# inline hmap22 #-}
