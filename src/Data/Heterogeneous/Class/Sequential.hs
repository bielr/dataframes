{-# language AllowAmbiguousTypes #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.Class.Sequential
  ( HIxed(..)
  , HSubseqI(..)
  , HSubseq
  , hsubseq
  , HQuotientI(..)
  , HQuotient
  , hsubseqSplit
  ) where

import Control.Lens.Type

import Data.Heterogeneous.Constraints
import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.TypeLevel.Subseq


-- Indexed access to the elements of an heterogeneous sequence

class HIxed hf where
    hix :: i < Length as => SNat i -> Lens' (hf f as) (f (as !! i))


-- field subsequences (different from subsets)

type HSubseqI :: forall k. HTyConK k -> [k] -> [k] -> [k] -> [k] -> [Peano] -> Constraint

class ReplaceSubseq ss ss' rs rs' is => HSubseqI hf ss ss' rs rs' is where
    hsubseqC :: Lens (hf f rs) (hf f rs') (hf f ss) (hf f ss')


type HSubseq :: forall k. HTyConK k -> [k] -> [k] -> [k] -> [k] -> Constraint
type HSubseq hf ss ss' rs rs' = HSubseqI hf ss ss' rs rs' (IndexesOf ss rs)


hsubseq :: forall ss ss' rs rs' hf f.
    HSubseq hf ss ss' rs rs'
    => Lens (hf f rs) (hf f rs') (hf f ss) (hf f ss')
hsubseq = hsubseqC
{-# inline hsubseq #-}


type HQuotientI :: forall k. HTyConK k -> [k] -> [k] -> [k] -> [Peano] -> Constraint

class HSubseqI hf ss '[] rs rs' is => HQuotientI hf ss rs rs' is where
    -- Isomorphism when ss' ~ '[]: splitting rs into ss and rs'
    --  view hsubseqC :: rs -> ss
    --  set hsubseqC HNil :: rs -> rs'
    --  view (hsubseqSplitC Refl) = view hsubseqC &&& set hsubseqC RNil
    --  rs is a permutation of to ss ++ rs'
    hsubseqSplitC :: Iso' (hf f rs) (hf f ss, hf f rs')


type HQuotient :: forall k. HTyConK k -> [k] -> [k] -> [k] -> Constraint
type HQuotient hf sub rs q = HQuotientI hf sub rs q (IndexesOf sub rs)


hsubseqSplit :: forall ss rs rs' hf f.
    HQuotient hf ss rs rs'
    => Iso' (hf f rs) (hf f ss, hf f rs')
hsubseqSplit = hsubseqSplitC
{-# inline hsubseqSplit #-}

