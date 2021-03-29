{-# language AllowAmbiguousTypes #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.Class.Member where

import Control.Lens (Lens, Lens', lens)

import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.TypeLevel.Subseq


type HGetI :: forall {k}. HTyConK k -> k -> [k] -> Peano -> Constraint

class (rs !! i) ~ r => HGetI hf r rs i | rs i -> r where
    hgetI :: hf f rs -> f r


type HSetI :: forall {k}. HTyConK k -> k -> k -> [k] -> [k] -> Peano -> Constraint

class
    ( HGetI hf r rs i
    , HGetI hf r' rs' i
    , ReplaceSubseqI '[r] '[r'] rs rs' '[i]
    )
    => HSetI hf r r' rs rs' i | rs r' i -> rs', rs' r i -> rs where

    hsetI :: f r' -> hf f rs -> hf f rs'

    hmemberI :: Lens (hf f rs) (hf f rs') (f r) (f r')
    hmemberI =
        lens (hgetI @hf @r @rs @i) (flip (hsetI @hf @r @r' @rs @rs' @i))
    {-# inline hmemberI #-}


type HGet :: forall k. HTyConK k -> k -> [k] -> Constraint
type HGet hf r rs = HGetI hf r rs (IndexOf r rs)


type HSet :: forall k. HTyConK k -> k -> k -> [k] -> [k] -> Constraint
type HSet hf r r' rs rs' = HSetI hf r r' rs rs' (IndexOf r rs)


hget :: forall r rs f hf.  HGet hf r rs => hf f rs -> f r
hget = hgetI @_ @_ @_ @(IndexOf r rs)


hset :: forall r r' rs rs' f hf. HSet hf r r' rs rs' => f r' -> hf f rs -> hf f rs'
hset = hsetI @_ @_ @_ @_ @_ @(IndexOf r rs)


hmember :: forall r r' rs rs' f g hf.
    (Functor g, HSet hf r r' rs rs')
    => (f r -> g (f r'))
    -> hf f rs -> g (hf f rs')
hmember = hmemberI @_ @_ @_ @_ @_ @(IndexOf r rs)


-- (efficient) indexed access to the elements of an heterogeneous sequence

type HIxed :: forall {k}. HTyConK k -> [k] -> Constraint

class HIxed hf as where
    hix' :: i < Length as => SNat i -> Lens' (hf f as) (f (as !! i))

    hix :: ReplaceSubseqI '[a] '[b] as bs '[i]
        => SNat i
        -> Lens (hf f as) (hf f bs) (f a) (f b)
