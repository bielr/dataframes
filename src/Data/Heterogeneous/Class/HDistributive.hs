{-# language UndecidableInstances #-}
module Data.Heterogeneous.Class.HDistributive where

import Data.Heterogeneous.Class.HFunctor
import Data.Heterogeneous.Functors ((:.), Compose(..))
import Data.Heterogeneous.TypeLevel (NatToInt, RLength)


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
        hcreate \i -> alg (fmap (view hix i) ghf)


    default hicotraverse ::
        (Functor g, HCreate hf as, HIxed hf)
        => (forall a. g (f a) -> h a)
        -> g (hf f as)
        -> hf h as
    hicotraverse alg ghf =
        hcreate \i -> alg i (fmap (view hix i) ghf)


--instance KnownLength as => HDistributive HSmallArray as where
--    hcotraverse alg grec =
--        generateSARec (getNatInt @(RLength as)) \i ->
--            alg $ fmap (`indexSARec` i) grec
--    {-# inline hcotraverse #-}
--    hicotraverse alg grec =
--        generateSARec (getNatInt @(RLength as)) \i ->
--            alg i $ fmap (`indexSARec` i) grec
--    {-# inline hicotraverse #-}


hdistribute :: (RDistributive hf as, Functor g) => g (hf f as) -> hf (g :. f) as
hdistribute = hcotraverse Compose
{-# inline hdistribute #-}
