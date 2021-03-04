{-# language AllowAmbiguousTypes #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
module Data.Heterogeneous.TypeLevel.Index where

import Prelude hiding ((!!))

import GHC.TypeLits (ErrorMessage(..))

import Data.Type.Equality

import Unsafe.Coerce

import Data.Heterogeneous.TypeLevel.List
import Data.Heterogeneous.TypeLevel.Nats



type (!!) :: forall k. [k] -> Peano -> k
type family as !! i where
    (a ': as) !! 'Zero     = a
    (a ': as) !! ('Succ i) = as !! i

infixl 9 !!

type IndexError :: forall k. [k] -> Peano -> ErrorMessage
type IndexError as i =
    'Text "Index "
    ':<>: 'ShowType (PeanoToNat i)
    ':<>: 'Text " out of bounds of "
    ':<>: 'ShowType as
    ':$$: 'Text "The given index is greater than the length of the list ("
    ':<>: 'ShowType (PeanoToNat (Length as))
    ':<>: 'Text ")"



type IndexAll :: forall k. [k] -> [Peano] -> [k]
type family IndexAll as is where
    IndexAll as       '[] = '[]
    IndexAll as (i ': is) = as !! i ': IndexAll as is


type IndexOf :: forall k. k -> [k] -> Peano
type family IndexOf a as where
    IndexOf a (a ': as) = 'Zero
    IndexOf a (b ': as) = 'Succ (IndexOf a as)


type IndexOfError :: forall k. k -> [k] -> ErrorMessage
type IndexOfError a as =
    'Text "The type "
    ':<>: 'ShowType a
    ':<>: 'Text " is not an element of the list "
    ':<>: 'ShowType as


type IndexesOf :: forall k. [k] -> [k] -> [Peano]
type family IndexesOf as bs where
    IndexesOf '[]       bs = '[]
    IndexesOf (a ': as) bs = IndexOf a bs ': IndexesOf as bs


type IndexesOfError :: forall k. [k] -> [k] -> ErrorMessage
type IndexesOfError as bs =
    'Text "Not all types in "
    ':<>: 'ShowType as
    ':<>: 'Text " were found in the list "
    ':<>: 'ShowType bs

type Drop :: forall k. Peano -> [k] -> [k]
type family Drop i as where
    Drop 'Zero     as        = as
    Drop ('Succ i) (a ': as) = Drop i as



-- type MapHKD :: forall k j. (k -> j) -> [k] -> [j]
-- type family MapHKD f xs where
--     MapHKD _       '[] = '[]
--     MapHKD f (x ': xs) = HKD f x ': MapHKD f xs


eqMapIndex :: forall k j (f :: k -> j) as i.
    i < Length as
    => (Map f as !! i) :~: f (as !! i)
eqMapIndex = unsafeCoerce (Refl @(f (as !! i)))
{-# inline eqMapIndex #-}


eqMapLength :: forall k j (f :: k -> j) as.
    Length as :~: Length (Map f as)
eqMapLength = unsafeCoerce (Refl @(Length as))
{-# inline eqMapLength #-}


eqDropIndex :: forall k i (as :: [k]) b bs.
    Drop i as ~ (b ': bs)
    => b :~: (as !! i)
eqDropIndex = unsafeCoerce (Refl @b)
{-# inline eqDropIndex #-}


eqDropNext :: forall k i (as :: [k]) b bs.
    Drop i as ~ (b ': bs)
    => bs :~: Drop ('Succ i) as
eqDropNext = unsafeCoerce (Refl @bs)
{-# inline eqDropNext #-}


eqDropLength :: forall k n (as :: [k]).
    Drop n as ~ '[]
    => n :~: Length as
eqDropLength = unsafeCoerce (Refl @n)
{-# inline eqDropLength #-}


leDropLength :: forall k i (as :: [k]) b bs.
    Drop i as ~ (b ': bs)
    => Truth (i <? Length as)
leDropLength = swear
{-# inline leDropLength #-}
