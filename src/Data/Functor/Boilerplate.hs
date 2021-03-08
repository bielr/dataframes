{-# language QuantifiedConstraints #-}
{-# language UndecidableInstances #-}
module Data.Functor.Boilerplate where

import Control.Lens.Iso (Iso, iso)

import Data.Kind
import Data.Functor.Identity
import Data.Functor.Compose

import Fcf.Core


type IsBoilerplate :: forall k. (k -> Type) -> Constraint

class IsBoilerplate (f :: k -> Type) where
    type Simplified f (a :: k) :: Type

    simplify :: f a -> Simplified f a
    complicate :: Simplified f a -> f a

    simplified :: Iso (f a) (f b) (Simplified f a) (Simplified f b)
    simplified = iso simplify complicate


instance IsBoilerplate Identity where
    type Simplified Identity a = a

    simplify = runIdentity
    complicate = Identity


instance IsBoilerplate (Compose f g) where
    type Simplified (Compose f g) a = f (g a)

    simplify = getCompose
    complicate = Compose


data Simplify :: (k -> Type) -> k -> Exp Type

type instance Eval (Simplify f a) = Simplified f a
