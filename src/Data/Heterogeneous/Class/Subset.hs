{-# language UndecidableInstances #-}
module Data.Heterogeneous.Class.Subset
  ( HSubset
  , hsubset
  , hcast
  ) where

import Data.Heterogeneous.TypeLevel


type SubsetIndices :: forall k. [k] -> [k] -> [Peano] -> Constraint
type SubsetIndices ss rs is = (IndexesOf ss rs ~ is, IndexAll rs is ~ ss)



type HSubsetI :: forall k. HTyConK k -> [k] -> [k] -> [Peano] -> Constraint

class SubsetIndices ss rs is => HSubsetI hf ss rs is where
    hsubsetC :: Functor g => (hf f ss -> g (hf f ss)) -> hf f rs -> g (hf f rs)

    hcastC :: hf f rs -> hf f ss


type HSubset :: forall k. HTyConK k -> [k] -> [k] -> Constraint
type HSubset hf ss rs = HSubsetI hf ss rs (IndexesOf ss rs)


hsubset :: forall ss rs hf f g.
    (Functor g, HSubset hf ss rs)
    => (hf f ss -> g (hf f ss))
    -> (hf f rs -> g (hf f rs))
hsubset = hsubsetC


hcast :: forall ss rs hf f.  HSubset hf ss rs => hf f rs -> hf f ss
hcast = hcastC
