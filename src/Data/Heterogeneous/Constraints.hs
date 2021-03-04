{-# language AllowAmbiguousTypes #-}
{-# language QuantifiedConstraints #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
module Data.Heterogeneous.Constraints
  ( Constraint
  , TrueC
  , ComposeC
  , FoldConstraints
  , Tupled(..)
  , All
  , AllF
  , constrained
  , iconstrained
  ) where

import Data.Kind (Constraint)

import Data.Heterogeneous.Constraints.Tupled
import Data.Heterogeneous.Constraints.TupledInstances ()
import Data.Heterogeneous.TypeLevel.Index
import Data.Heterogeneous.TypeLevel.List
import Data.Heterogeneous.TypeLevel.Nats


type TrueC :: forall k. k -> Constraint

class TrueC a
instance TrueC a


type ComposeC :: forall k j. (j -> Constraint) -> (k -> j) -> k -> Constraint

class c (f a) => ComposeC c f a
instance c (f a) => ComposeC c f a


type All :: forall k. (k -> Constraint) -> [k] -> Constraint
type All c as = Tupled (Map c as)


type AllF :: forall k j. (j -> Constraint) -> (k -> j) -> [k] -> Constraint
type AllF c f as = All c (Map f as)


constrained :: forall c as r i.
    (All c as, i < Length as)
    => (c (as !! i) => r)
    -> SNat i
    -> r
constrained r =
    assuming (eqMapLength @_ @_ @c @as) $ \i ->
    assuming (eqMapIndex @_ @_ @c @as @i) $
        instAt @(Map c as) i r
{-# inline constrained #-}


iconstrained :: forall c as r i.
    (All c as, i < Length as)
    => (c (as !! i) => SNat i -> r)
    -> SNat i
    -> r
iconstrained f =
    assuming (eqMapLength @_ @_ @c @as) $ \i ->
    assuming (eqMapIndex @_ @_ @c @as @i) $
        instAt @(Map c as) i (f i)
{-# inline iconstrained #-}
