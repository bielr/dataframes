{-# language AllowAmbiguousTypes #-}
module Data.Heterogeneous.Class.HApply
  ( HApply(..)
  ) where

import Data.Heterogeneous.Class.HFunctor
import Data.Heterogeneous.TypeLevel


type HApply :: forall k. HTyConK k -> [k] -> Constraint

class HFunctor hf as => HApply hf as where
    hzipWith ::
        (forall x. f x -> g x -> h x)
        -> hf f as
        -> hf g as
        -> hf h as
    hzipWith f = hizipWith \_ -> f


    hizipWith ::
        (forall i. i < Length as => SNat i -> f (as !! i) -> g (as !! i) -> h (as !! i))
        -> hf f as
        -> hf g as
        -> hf h as
