{-# language UndecidableInstances #-}
module Data.Heterogeneous.TypeLevel.List where

import Prelude hiding ((++))

import GHC.TypeLits

import Data.Heterogeneous.TypeLevel.Kind
import Data.Heterogeneous.TypeLevel.Peano


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
