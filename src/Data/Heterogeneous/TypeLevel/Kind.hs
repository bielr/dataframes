{-# language UndecidableInstances #-}
module Data.Heterogeneous.TypeLevel.Kind
  ( Type
  , Constraint
  , KindOf
  , Nat
  , HTyConK
  , HPolyTyConK
  , NAryTyConK
  ) where

import GHC.TypeNats

import Data.Kind (Constraint, Type)

import Data.Heterogeneous.TypeLevel.Peano


type KindOf :: forall k. k -> Type
type KindOf (a :: k) = k


type HTyConK :: Type -> Type
type HTyConK k = (k -> Type) -> [k] -> Type


type HPolyTyConK :: Type
type HPolyTyConK = forall k. HTyConK k


type NAryTyConK :: Peano -> Type -> Type -> Type

type family NAryTyConK n argk resk where
    NAryTyConK 'Zero     argk resk = resk
    NAryTyConK ('Succ n) argk resk = argk -> NAryTyConK n argk resk

