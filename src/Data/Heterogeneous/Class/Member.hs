{-# language AllowAmbiguousTypes #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.Class.Member where

import Control.Lens (Lens, Lens', lens)

import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.TypeLevel.Subseq


type HGetI :: forall {k}. HTyConK k -> k -> [k] -> Peano -> Constraint

class (rs !! i) ~ r => HGetI hf r rs i | rs i -> r where
    hgetC :: hf f rs -> f r


type HSetI :: forall {k}. HTyConK k -> k -> k -> [k] -> [k] -> Peano -> Constraint

class
    ( HGetI hf r rs i
    , HGetI hf r' rs' i
    , ReplaceSubseq '[r] '[r'] rs rs' '[i]
    )
    => HSetI hf r r' rs rs' i where

    hsetC :: f r' -> hf f rs -> hf f rs'

    hmemberC :: Lens (hf f rs) (hf f rs') (f r) (f r')
    hmemberC =
        lens (hgetC @hf @r @rs @i) (flip (hsetC @hf @r @r' @rs @rs' @i))
    {-# inline hmemberC #-}


type HGet :: forall k. HTyConK k -> k -> [k] -> Constraint
type HGet hf r rs = HGetI hf r rs (IndexOf r rs)


type HSet :: forall k. HTyConK k -> k -> k -> [k] -> [k] -> Constraint
type HSet hf r r' rs rs' = HSetI hf r r' rs rs' (IndexOf r rs)


hget :: forall r rs f hf.  HGet hf r rs => hf f rs -> f r
hget = hgetC @_ @_ @_ @(IndexOf r rs)


hset :: forall r r' rs rs' f hf. HSet hf r r' rs rs' => f r' -> hf f rs -> hf f rs'
hset = hsetC @_ @_ @_ @_ @_ @(IndexOf r rs)


hmember :: forall r r' rs rs' f g hf.
    (Functor g, HSet hf r r' rs rs')
    => (f r -> g (f r'))
    -> hf f rs -> g (hf f rs')
hmember = hmemberC


-- (efficient) indexed access to the elements of an heterogeneous sequence

class HIxed hf where
    hix :: i < Length as => SNat i -> Lens' (hf f as) (f (as !! i))
