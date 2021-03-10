{-# language AllowAmbiguousTypes #-}
{-# language MagicHash #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.TypeLevel.SNat
  ( module Peano
  , PredPeano
  , Truth
  , type (<?)
  , type (<)
  , swear
  , assuming
  , swearing
  , leSucc
  , transLe
  , lePredTail
  , SNat(..)
  , getSNat
  , toSNat
  , zeroNat
  , succNat
  , unsafePredNat
  , predNat
  , caseNat
  , succNatUpTo
  , foldrNatInts
  , foldlNatInts'
  , mapNatInts
  ) where

import GHC.TypeLits
import GHC.Exts (proxy#)

import Data.Kind (Constraint, Type)
import Data.Type.Equality

import Unsafe.Coerce

import Data.Heterogeneous.TypeLevel.List
import Data.Heterogeneous.TypeLevel.Peano as Peano


type PredPeano :: Peano -> Peano
type family PredPeano i where
    PredPeano 'Zero     = TypeError ('Text "Zero has no predecessor")
    PredPeano ('Succ n) = n


type Truth :: Bool -> Type
type Truth b = b :~: 'True


type CmpPeano :: Peano -> Peano -> Ordering
type family CmpPeano n m where
    CmpPeano 'Zero     ('Succ m) = 'LT
    CmpPeano 'Zero     'Zero     = 'EQ
    CmpPeano ('Succ n) 'Zero     = 'GT
    CmpPeano ('Succ n) ('Succ m) = CmpPeano n m


type (<?) :: Peano -> Peano -> Bool
type i <? n = CmpPeano i n == 'LT


type (<) :: Peano -> Peano -> Constraint

class (i <? n) ~ 'True => i < n
instance {-# incoherent #-} (i <? n) ~ 'True => i < n



swear :: Truth b
swear = unsafeCoerce (Refl @'True)


assuming :: (a :~: b) -> (a ~ b => r) -> r
assuming Refl r = r


swearing :: forall b r. (b ~ 'True => r) -> r
swearing = assuming (swear @b)


leSucc :: Truth (i <? 'Succ i)
leSucc = swear


transLe :: (a < b, b < c) => Truth (a <? c)
transLe = swear


lePredTail :: ('Succ i <? Length (c ': cs)) :~: (i <? Length cs)
lePredTail = Refl


predNonZero :: forall i n. (i < n) => n :~: 'Succ (PredPeano n)
predNonZero = unsafeCoerce (Refl @n)


-- unsafe (but fast and convenient) singleton for Nat
type SNat :: Peano -> Type
newtype SNat i = SNat { snat :: Int }


getSNat :: forall i. KnownPeano i => SNat i
getSNat = SNat (peanoInt @i)
{-# inline getSNat #-}


toSNat :: forall i. KnownNat i => SNat (NatToPeano i)
toSNat = SNat (fromInteger (natVal' @i proxy#))
{-# inline toSNat #-}


zeroNat :: SNat 'Zero
zeroNat = SNat 0
{-# inline zeroNat #-}


unsafePredNat :: SNat i -> SNat (PredPeano i)
unsafePredNat (SNat i) = SNat (i-1)
{-# inline unsafePredNat #-}


predNat :: SNat ('Succ i) -> SNat i
predNat (SNat i) = SNat (i-1)
{-# inline predNat #-}


succNat :: SNat i -> SNat ('Succ i)
succNat (SNat i) = SNat (i+1)
{-# inline succNat #-}


caseNat :: forall i r.
    SNat i
    -> (i ~ 'Zero => r)
    -> (i ~ 'Succ  (PredPeano i) => r)
    -> r
caseNat (SNat i) z s =
    case i of
      0 ->
          case unsafeCoerce (Refl @'Zero) :: i :~: 'Zero of
            Refl -> z
      _ ->
          swearing @('Zero <? i) $
            assuming (predNonZero @'Zero @i) s
{-# inline caseNat #-}


succNatUpTo :: forall i n r.
    i < n
    => SNat n
    -> SNat i
    -> ('Succ i ~ n => r)
    -> ('Succ i < n => r)
    -> r
succNatUpTo n i endr r
    | snat n == snat i + 1 = assuming @('Succ i) @n (unsafeCoerce (Refl @n)) endr
    | otherwise            = swearing @('Succ i <? n) r
{-# inline succNatUpTo #-}


foldrNatInts :: forall n b. SNat n -> (forall i. i < n => SNat i -> b -> b) -> b -> b
foldrNatInts n f z = caseNat n z (go zeroNat z)
  where
    go :: j < n => SNat j -> b -> b
    go !j b = succNatUpTo n j (f j b) (f j (go (succNat j) b))
{-# inline foldrNatInts #-}


-- reversed foldl'
foldlNatInts' :: forall n b. SNat n -> (forall i. i < n => b -> SNat i -> b) -> b -> b
foldlNatInts' n f z = caseNat n z (go zeroNat z)
  where
    go :: j < n => SNat j -> b -> b
    go !j !b = succNatUpTo n j (f b j) (go (succNat j) (f b j))
{-# inline foldlNatInts' #-}


mapNatInts :: forall n r. SNat n -> (forall i. i < n => SNat i -> r) -> [r]
mapNatInts n f = foldrNatInts n (\i rs -> f i : rs) []
{-# inline mapNatInts #-}
