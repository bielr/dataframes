{-# language UndecidableInstances #-}
module Data.Heterogeneous.TypeLevel.List where

import Prelude hiding ((++))

import GHC.TypeLits

import Data.Heterogeneous.TypeLevel.Kind
import Data.Heterogeneous.TypeLevel.Peano


type Map :: forall k j. (k -> j) -> [k] -> [j]
type family Map f xs where
    Map _       '[] = '[]
    Map f (x ': xs) = f x ': Map f xs


type (++) :: forall k. [k] -> [k] -> [k]
type family as ++ bs where
    '[]       ++ bs = bs
    (a ': as) ++ bs = a ': (as ++ bs)

infixr 5 ++


type Length :: forall k. [k] -> Peano
type family Length as where
    Length (x ': xs) = 'Succ (Length xs)
    Length '[]       = 'Zero


type KnownLength :: forall k. [k] -> Constraint
type KnownLength as = KnownPeano (Length as)


type Delete :: forall k. k -> [k] -> [k]
type family Delete a as where
    Delete a (a ': as) = as
    Delete a (b ': as) = Delete a as

type DeleteError :: forall k. k -> [k] -> ErrorMessage
type DeleteError a as =
    'Text "Type " ':<>: 'ShowType a ':<>: 'Text " not found in list " ':<>: 'ShowType as


type DeleteAll :: forall k. [k] -> [k] -> [k]
type family DeleteAll as bs where
    DeleteAll '[]       bs = bs
    DeleteAll (a ': as) bs = DeleteAll as (Delete a bs)


type AppTyCon :: forall k j. forall (args :: [k]) -> TyCon (Length args) k j -> j

type family AppTyCon args f where
    AppTyCon '[]       f = f
    AppTyCon (a ': as) f = AppTyCon as (f a)


type AppliedTyCon :: forall k j. forall (args :: [k]) -> TyCon (Length args) k j -> j -> Constraint

class r ~ AppTyCon args f => AppliedTyCon args f r | f r -> args, args r -> f, f args -> r
instance f ~ r                   => AppliedTyCon '[] f r
instance AppliedTyCon as (f a) r => AppliedTyCon (a ': as) f r
