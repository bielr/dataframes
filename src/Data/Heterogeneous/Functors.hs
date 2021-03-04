module Data.Heterogeneous.Functors
  ( module Exports
  , (:.)
  ) where

import Data.Kind (Type)

import Data.Functor.Identity as Exports
import Data.Functor.Compose  as Exports


type (:.) :: forall i j. (j -> Type) -> (i -> j) -> i -> Type
type (:.) = Compose
