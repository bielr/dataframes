{-# language UndecidableInstances #-}
module Data.Heterogeneous.TypeLevel.Kind
  ( Constraint
  , KindOf
  , Nat
  , HTyCon
  , Type
  , TyCon
  ) where

import GHC.TypeNats

import Data.Kind (Constraint, Type)

import Data.Heterogeneous.TypeLevel.Peano


type KindOf :: forall k. k -> Type
type KindOf (a :: k) = k


type HTyCon :: Type -> Type
type HTyCon k = (k -> Type) -> [k] -> Type


type TyCon :: Peano -> Type -> Type -> Type

type family TyCon n argk resk where
    TyCon 'Zero     argk resk = resk
    TyCon ('Succ n) argk resk = argk -> TyCon n argk resk

