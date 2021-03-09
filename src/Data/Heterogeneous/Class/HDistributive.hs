{-# language UndecidableInstances #-}
module Data.Heterogeneous.Class.HDistributive where

import Control.Lens (view)

import Data.Heterogeneous.Class.HCreate
import Data.Heterogeneous.Class.HFunctor
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.Functors ((:.), Compose(..))
import Data.Heterogeneous.TypeLevel


type HDistributive :: forall k. HTyConK k -> [k] -> Constraint

class HFunctor hf => HDistributive hf as where
    hcotraverse ::
        Functor g
        => (forall a. g (f a) -> h a)
        -> g (hf f as)
        -> hf h as

    hicotraverse ::
        Functor g
        => (forall i. i < Length as => SNat i -> g (f (as !! i)) -> h (as !! i))
        -> g (hf f as)
        -> hf h as

    default hcotraverse ::
        (Functor g, HCreate hf as, HIxed hf)
        => (forall a. g (f a) -> h a)
        -> g (hf f as)
        -> hf h as
    hcotraverse alg ghf =
        hcreate \i -> alg (fmap (view (hix i)) ghf)
    {-# inline hcotraverse #-}

    default hicotraverse ::
        (Functor g, HCreate hf as, HIxed hf)
        => (forall i. i < Length as => SNat i -> g (f (as !! i)) -> h (as !! i))
        -> g (hf f as)
        -> hf h as
    hicotraverse alg ghf =
        hcreate \i -> alg i (fmap (view (hix i)) ghf)
    {-# inline hicotraverse #-}


hdistribute :: (HDistributive hf as, Functor g) => g (hf f as) -> hf (g :. f) as
hdistribute = hcotraverse Compose
{-# inline hdistribute #-}
