{-# language AllowAmbiguousTypes #-}
{-# language QuantifiedConstraints #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
module Data.Heterogeneous.Constraints
  ( Constraint
  , Dict(..)
  , TrueC
  , ComposeExpC
  , ComposeC
  , FoldConstraints
  , Tupled(..)
  , All
  , AllE
  , AllF
  , constrained
  , iconstrained
  ) where

import Data.Constraint (Dict(..))

import Data.Heterogeneous.Constraints.Tupled
import Data.Heterogeneous.Constraints.TupledInstances ()
import Data.Heterogeneous.TypeLevel


type TrueC :: forall k. k -> Constraint

class TrueC a
instance TrueC a


type ComposeExpC :: forall k j. (j -> Constraint) -> (k -> Exp j) -> k -> Constraint

class c (f @@ a) => ComposeExpC c f a
instance c (f @@ a) => ComposeExpC c f a


type ComposeC :: forall k j. (j -> Constraint) -> (k -> j) -> k -> Constraint
type ComposeC c f = ComposeExpC c (Pure1 f)


type All :: forall k. (k -> Constraint) -> [k] -> Constraint
type All c as = Tupled (Map c as)


type AllE :: forall k j. (j -> Constraint) -> (k -> Exp j) -> [k] -> Constraint
type AllE c f as = All (ComposeExpC c f) as


type AllF :: forall k j. (j -> Constraint) -> (k -> j) -> [k] -> Constraint
type AllF c f as = All (ComposeC c f) as


constrained :: forall c as r i.
    (All c as, i < Length as)
    => (c (as !! i) => r)
    -> SNat i
    -> r
constrained r =
    assuming (eqMapLength @c @as) \i ->
    assuming (eqMapIndex @c @as @i) $
        instAt @(Map c as) i r
{-# inline constrained #-}


iconstrained :: forall c as r i.
    (All c as, i < Length as)
    => (c (as !! i) => SNat i -> r)
    -> SNat i
    -> r
iconstrained f =
    assuming (eqMapLength @c @as) \i ->
    assuming (eqMapIndex @c @as @i) $
        instAt @(Map c as) i (f i)
{-# inline iconstrained #-}
