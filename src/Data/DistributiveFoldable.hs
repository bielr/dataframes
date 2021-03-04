{-# language GeneralizedNewtypeDeriving #-}
module Data.DistributiveFoldable where

import Control.Lens.Internal.Setter (Settable(..))
import Control.Lens.Indexed (FunctorWithIndex(imap), FoldableWithIndex(ifoldMap))

import Data.Distributive
import Data.Foldable
import Data.Functor (void)
import Data.Functor.Const
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Monoid (Ap(..))
import Data.Profunctor.Unsafe


-- Generalization of Distributive by providing Foldable t
-- This allows instances for monoids with phantom argument like Const m
class Functor f => DistributiveFoldable f where
    {-# minimal foldDistribute | foldCollect #-}

    foldDistribute :: (Functor t, Foldable t) => t (f a) -> f (t a)
    foldDistribute = foldCollect id
    {-# inline foldDistribute #-}

    foldCollect :: (Functor t, Foldable t) => (a -> f b) -> t a -> f (t b)
    foldCollect f = foldDistribute . fmap f
    {-# inline foldCollect #-}

    ifoldCollect :: (FunctorWithIndex i t, FoldableWithIndex i t) => (i -> a -> f b) -> t a -> f (t b)
    ifoldCollect f = foldDistribute . imap f
    {-# inline ifoldCollect #-}


foldDistributeDefault :: (Contravariant f, Applicative f, Foldable t) => t (f a) -> f (t a)
foldDistributeDefault = ($< ()) . getAp #. foldMap (Ap #. void)
{-# inline foldDistributeDefault #-}


foldCollectDefault :: (Contravariant f, Applicative f, Foldable t) => (a -> f b) -> t a -> f (t b)
foldCollectDefault f = ($< ()) . getAp #. foldMap (Ap #. void . f)
{-# inline foldCollectDefault #-}


ifoldCollectDefault :: (Contravariant f, Applicative f, FoldableWithIndex i t) => (i -> a -> f b) -> t a -> f (t b)
ifoldCollectDefault f = ($< ()) . getAp #. ifoldMap (\i -> Ap #. void . f i)
{-# inline ifoldCollectDefault #-}


-- most useful cases for lens

instance Monoid m => DistributiveFoldable (Const m) where
    foldDistribute = Const #. getConst #. fold
    {-# inline foldDistribute #-}

    foldCollect f = Const #. getConst #. foldMap f
    {-# inline foldCollect #-}

    ifoldCollect f = Const #. getConst #. ifoldMap f
    {-# inline ifoldCollect #-}


instance DistributiveFoldable Identity where
    foldCollect = collect
    {-# inline foldCollect #-}

    foldDistribute = distribute
    {-# inline foldDistribute #-}


-- class DistributiveFoldable f => Distributive f

-- Workaround a la WrappedMonad

newtype WrappedDistributive f a = WrappedDistributive { unwrapDistributive :: f a }
    deriving (Eq, Ord, Show, Semigroup, Monoid, Functor, Applicative, Monad, Foldable, Contravariant)


instance Traversable f => Traversable (WrappedDistributive f) where
    traverse f (WrappedDistributive fa) = WrappedDistributive <$> traverse f fa
    {-# inline traverse #-}


instance Settable f => Settable (WrappedDistributive f) where
    taintedDot f = WrappedDistributive #. taintedDot f
    {-# inline taintedDot #-}

    untaintedDot f = untaintedDot (unwrapDistributive #. f)
    {-# inline untaintedDot #-}

    untainted = untainted .# unwrapDistributive
    {-# inline untainted #-}


instance Distributive f => DistributiveFoldable (WrappedDistributive f) where
    foldDistribute = distribute
    {-# inline foldDistribute #-}

    foldCollect = collect
    {-# inline foldCollect #-}


instance Distributive f => Distributive (WrappedDistributive f) where
    collect f = WrappedDistributive #. collect (unwrapDistributive #. f)
    {-# inline collect #-}


newtype WrappedBivariant f a = WrappedBivariant { unwrapBivariant :: f a }
    deriving (Eq, Ord, Show, Semigroup, Monoid, Functor, Applicative, Monad, Foldable, Contravariant)


instance (Contravariant f, Applicative f) => DistributiveFoldable (WrappedBivariant f) where
    foldDistribute = foldDistributeDefault
    {-# inline foldDistribute #-}

    foldCollect = foldCollectDefault
    {-# inline foldCollect #-}

    ifoldCollect = ifoldCollectDefault
    {-# inline ifoldCollect #-}


