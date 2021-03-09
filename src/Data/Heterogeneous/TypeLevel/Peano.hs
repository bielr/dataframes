{-# language AllowAmbiguousTypes #-}
{-# language MagicHash #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Heterogeneous.TypeLevel.Peano
  ( Peano(..)
  , KnownNat
  , KnownPeano
  , KnownNats(..)
  , KnownPeanos
  , NatToPeano
  , PeanoToNat
  , PeanosToNats
  , peanoInt
  , peanoInts
  , ForcePeano
  , ForcePeanos
  ) where

import GHC.Prim (proxy#)
import GHC.TypeLits

import Data.Kind (Constraint)


data Peano = Zero | Succ Peano


type PeanoToNat :: Peano -> Nat
type family PeanoToNat p where
    PeanoToNat 'Zero     = 0
    PeanoToNat ('Succ n) = 1 + PeanoToNat n


type NatToPeano :: Nat -> Peano
type family NatToPeano n where
    NatToPeano 0 = 'Zero
    NatToPeano n = 'Succ (NatToPeano (n-1))


type KnownPeano :: Peano -> Constraint
type KnownPeano p = KnownNat (PeanoToNat p)


peanoInt :: forall p. KnownPeano p => Int
peanoInt = fromInteger (natVal' @(PeanoToNat p) proxy#)


type KnownNats :: [Nat] -> Constraint

class KnownNats is where
    natVals :: [Int]

instance KnownNats '[] where
    natVals = []

instance (KnownNat i, KnownNats is) => KnownNats (i ': is) where
    natVals = fromInteger (natVal' @i proxy#) : natVals @is


type family PeanosToNats is where
    PeanosToNats '[]       = '[]
    PeanosToNats (i ': is) = PeanoToNat i ': PeanosToNats is

type KnownPeanos :: [Peano] -> Constraint
type KnownPeanos is = KnownNats (PeanosToNats is)


peanoInts :: forall is. KnownPeanos is => [Int]
peanoInts = natVals @(PeanosToNats is)



-- for use with IfStuck

type ForcePeano :: Peano -> ()
type family ForcePeano i where
    ForcePeano 'Zero     = '()
    ForcePeano ('Succ i) = ForcePeano i


type ForcePeanos :: [Peano] -> ()
type family ForcePeanos is where
    ForcePeanos '[]             = '()
    ForcePeanos ('Zero   ': is) = ForcePeanos is
    ForcePeanos ('Succ i ': is) = ForcePeanos (i ': is)

