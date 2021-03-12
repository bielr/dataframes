{-# language UndecidableInstances #-}
module Data.Heterogeneous.TypeLevel.List where

import Prelude hiding ((++))

import Fcf.Core
import GHC.TypeLits

import Data.Heterogeneous.TypeLevel.Kind
import Data.Heterogeneous.TypeLevel.Peano


type Map :: (i -> j) -> [i] -> [j]
type family Map f xs = ys where
    Map _       '[] = '[]
    Map f (x ': xs) = f x ': Map f xs


type MapExp :: forall k j. (k -> Exp j) -> [k] -> Exp [j]
data MapExp f xs :: Exp [j]

type instance Eval (MapExp f '[])       = '[]
type instance Eval (MapExp f (x ': xs)) = Eval (f x) ': Eval (MapExp f xs)


-- workaround because GHC can't understand that Map is injective for fixed i
type Mapped :: forall {i} {j}. (i -> j) -> [i] -> [j] -> Constraint

class ys ~ Map f xs => Mapped f (xs :: [i]) (ys :: [j]) | i ys -> xs
instance Mapped f '[] '[]
instance (y ~ f x, Mapped f xs ys) => Mapped f (x ': xs) (y ': ys)


type ZipWith :: forall i j k. (i -> j -> k) -> [i] -> [j] -> [k]
type family ZipWith f is js where
    ZipWith _       '[]       '[] = '[]
    ZipWith f (i ': is) (j ': js) = f i j ': ZipWith f is js


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


type ApplyTyCon :: forall k j. forall (args :: [k]) -> NAryTyConK (Length args) k j -> j

type family ApplyTyCon args f where
    ApplyTyCon '[]       f = f
    ApplyTyCon (a ': as) f = ApplyTyCon as (f a)


-- workaround because GHC can't understand that ApplyTyCon is injective
type AppliedTyCon :: forall k j. forall (args :: [k]) -> NAryTyConK (Length args) k j -> j -> Constraint

class r ~ ApplyTyCon args f => AppliedTyCon args f r | f r -> args, args r -> f, f args -> r
instance f ~ r                   => AppliedTyCon '[] f r
instance AppliedTyCon as (f a) r => AppliedTyCon (a ': as) f r
