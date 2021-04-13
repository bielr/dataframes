{-# language QuantifiedConstraints #-}
{-# language UndecidableInstances #-}
module Data.Functor.Boilerplate where

import Control.Lens.Iso (Iso, iso)
import Data.Profunctor.Unsafe ((#.), (.#))

import Data.Kind
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.Vector qualified as VB

import Fcf.Core


type RemoveBoilerplate :: forall {k}. (k -> Type) -> Constraint

class RemoveBoilerplate (f :: k -> Type) where
    type Simplified f (a :: k) :: Type
    type Simplified f a = f a

    simplify :: f a -> Simplified f a

    complicate :: Simplified f a -> f a

    simplified :: Iso (f a) (f b) (Simplified f a) (Simplified f b)
    simplified = iso simplify complicate

    default simplify :: Simplified f a ~ f a => f a -> Simplified f a
    simplify = id

    default complicate :: Simplified f a ~ f a => Simplified f a -> f a
    complicate = id


instance RemoveBoilerplate (Const a) where
    type Simplified (Const a) b = a

    simplify = getConst
    complicate = Const


instance RemoveBoilerplate Identity where
    type Simplified Identity a = a

    simplify = runIdentity
    complicate = Identity


instance
    (Functor f, RemoveBoilerplate f, RemoveBoilerplate g)
    => RemoveBoilerplate (Compose f g) where

    type Simplified (Compose f g) a = Simplified f (Simplified g a)

    simplify = simplify . fmap simplify .# getCompose
    complicate = Compose #. fmap complicate . complicate


instance RemoveBoilerplate []
instance RemoveBoilerplate ((,) x)
instance RemoveBoilerplate ((->) a)
instance RemoveBoilerplate (Either e)
instance RemoveBoilerplate IO
instance RemoveBoilerplate Maybe
instance RemoveBoilerplate VB.Vector


type Simplify :: (k -> Type) -> k -> Exp Type
data Simplify f a :: Exp Type

type instance Eval (Simplify f a) = Simplified f a
