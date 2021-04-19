{-# language UndecidableInstances #-}
module Data.Heterogeneous.TypeLevel.Apply
    ( type (@@)
    , Exp
    , Pure
    , Pure1
    , FMap

    , UnApply
    , UnApplyExp
    , Map
    , UnMap
    , Mapped

    , ZipWith
    , UnZipWith1
    , UnZipWith2
    , ZippedWith

    , ApplyTyCon
    , AppliedTyCon
    ) where

import GHC.TypeLits
import Fcf.Core
import Fcf.Combinators (Pure, Pure1)
import Fcf.Class.Functor (FMap)

import Data.Heterogeneous.TypeLevel.Kind
import Data.Heterogeneous.TypeLevel.List


-- 1-ary type constructors

type UnApply :: (i -> j) -> j -> i
type family UnApply f y where
    UnApply f (f x) = x
    UnApply f y     = TypeError (
        'ShowType y
        ':<>: 'Text " is not of the form "
        ':<>: 'ShowType f
        ':<>: 'Text " x")

type UnApplyExp :: (i -> j) -> j -> Exp i
data UnApplyExp f y :: Exp i

type instance Eval (UnApplyExp f y) = UnApply f y


type Map :: (i -> j) -> [i] -> [j]
type Map f xs = FMap (Pure1 f) @@ xs


type UnMap :: (i -> j) -> [j] -> [i]
type UnMap f ys = FMap (UnApplyExp f) @@ ys


-- workaround because GHC can't understand that Map is injective for fixed i
type Mapped :: forall {i} {j}. (i -> j) -> [i] -> [j] -> Constraint
type Mapped f xs ys = (xs ~ UnMap f ys, ys ~ Map f xs)


-- binary type constructors

type ZipWith :: forall i j k. (i -> j -> k) -> [i] -> [j] -> [k]
type family ZipWith f is js where
    ZipWith _       '[]       '[] = '[]
    ZipWith f (i ': is) (j ': js) = f i j ': ZipWith f is js


type UnZipWith1 :: forall i j k. (i -> j -> k) -> [k] -> [i]
type family UnZipWith1 f ks where
    UnZipWith1 _           '[] = '[]
    UnZipWith1 f (f i _ ': ks) = i ': UnZipWith1 f ks


type UnZipWith2 :: forall i j k. (i -> j -> k) -> [k] -> [j]
type family UnZipWith2 f ks where
    UnZipWith2 _           '[] = '[]
    UnZipWith2 f (f _ j ': ks) = j ': UnZipWith2 f ks


type ZippedWith :: forall {i} {j} {k}. (i -> j -> k) -> [i] -> [j] -> [k] -> Constraint
type ZippedWith f xs ys zs =
    ( zs ~ ZipWith f xs ys
    , xs ~ UnZipWith1 f zs
    , ys ~ UnZipWith2 f zs
    )


-- N-ary type constructors

type ApplyTyCon :: forall k j. forall (args :: [k]) -> NAryTyConK (Length args) k j -> j

type family ApplyTyCon args f where
    ApplyTyCon '[]       f = f
    ApplyTyCon (a ': as) f = ApplyTyCon as (f a)


-- workaround because GHC can't understand that ApplyTyCon is injective on each argument
type AppliedTyCon :: forall k j. forall (args :: [k]) -> NAryTyConK (Length args) k j -> j -> Constraint

class r ~ ApplyTyCon args f => AppliedTyCon args f r | f r -> args, args r -> f, f args -> r
instance f ~ r                   => AppliedTyCon '[] f r
instance AppliedTyCon as (f a) r => AppliedTyCon (a ': as) f r

