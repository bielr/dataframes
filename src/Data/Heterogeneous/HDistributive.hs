{-# language UndecidableInstances #-}
module Data.Heterogeneous.HDistributive where

import Data.Vinyl.Functor ((:.), Compose(..))
import Data.Vinyl.TypeLevel (NatToInt, RLength)

import Data.Heterogeneous.RFunctor
import Data.Vinyl.Extra.Kind
import Data.Vinyl.Extra.SARec (SARec, generateSARec, indexSARec)
import Data.Vinyl.Extra.TypeLevel


type RDistributive :: forall k. RecordKind k -> [k] -> Constraint

class RFunctor rec => RDistributive rec as where
    rcotraverse ::
        Functor g
        => (forall a. g (f a) -> h a)
        -> g (rec f as)
        -> rec h as

    ricotraverse ::
        Functor g
        => (forall i. i < RLength as => NatInt i -> g (f (as !! i)) -> h (as !! i))
        -> g (rec f as)
        -> rec h as


instance NatToInt (RLength as) => RDistributive SARec as where
    rcotraverse alg grec =
        generateSARec (getNatInt @(RLength as)) \i ->
            alg $ fmap (`indexSARec` i) grec
    {-# inline rcotraverse #-}

    ricotraverse alg grec =
        generateSARec (getNatInt @(RLength as)) \i ->
            alg i $ fmap (`indexSARec` i) grec
    {-# inline ricotraverse #-}


rdistribute :: (RDistributive rec as, Functor g) => g (rec f as) -> rec (g :. f) as
rdistribute = rcotraverse Compose
{-# inline rdistribute #-}
