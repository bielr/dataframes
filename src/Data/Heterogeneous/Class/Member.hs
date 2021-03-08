{-# language AllowAmbiguousTypes #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.Class.Member where

import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.TypeLevel.Subseq


type HGetI :: forall k. HTyConK k -> k -> [k] -> Peano -> Constraint

class i ~ IndexOf r rs => HGetI hf r rs i | i r -> rs, rs i -> r where
    hIxGetC :: hf f rs -> f r


type HSetI :: forall k. HTyConK k -> k -> k -> [k] -> [k] -> Peano -> Constraint

class
    ( HGetI hf r rs i
    , HGetI hf r' rs' i
    , ReplaceSubseq '[r] '[r'] rs rs' '[i]
    )
    => HSetI hf r r' rs rs' i where

    hsetC :: f r' -> hf f rs -> hf f rs'
    hmemberC :: Functor g => (f r -> g (f r')) -> hf f rs -> g (hf f rs')


type HGet :: forall k. HTyConK k -> k -> [k] -> Constraint
type HGet hf r rs = HGetI hf r rs (IndexOf r rs)


type HSet :: forall k. HTyConK k -> k -> k -> [k] -> [k] -> Constraint
type HSet hf r r' rs rs' = HSetI hf r r' rs rs' (IndexOf r rs)


hget :: forall r rs f hf.  HGet hf r rs => hf f rs -> f r
hget = hIxGetC


hset :: forall r r' rs rs' f hf. HSet hf r r' rs rs' => f r' -> hf f rs -> hf f rs'
hset = hsetC


hmember :: forall r r' rs rs' f g hf.
    (Functor g, HSet hf r r' rs rs')
    => (f r -> g (f r'))
    -> hf f rs -> g (hf f rs')
hmember = hmemberC
