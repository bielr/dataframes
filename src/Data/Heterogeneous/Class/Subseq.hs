{-# language AllowAmbiguousTypes #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.Class.Subseq
  ( HSubseqI(..)
  , HSubseq
  , hsubseq
  , HSubseq'
  , hsubseq'
  , testSubseqInstance
  , HQuotientI(..)
  , HQuotient
  , hsubseqSplit
  , IsSubseqWithError
  ) where

import Control.Lens (view, set)
import Control.Lens.Type
import Data.Functor.Identity

import Data.Heterogeneous.Class.HMonoid
import Data.Heterogeneous.Constraints
import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.TypeLevel.Subseq


-- field subsequences (different from subsets)

type HSubseqI :: forall {k}. HTyConK k -> [k] -> [k] -> [k] -> [k] -> [Peano] -> Constraint

class ReplaceSubseqI ss ss' rs rs' is => HSubseqI hf ss ss' rs rs' is where
    hsubseqI :: Lens (hf f rs) (hf f rs') (hf f ss) (hf f ss')


type HSubseq :: forall k. HTyConK k -> [k] -> [k] -> [k] -> [k] -> Constraint
type HSubseq hf ss ss' rs rs' =
    ( ReplaceSubseq ss ss' rs rs'
    , HSubseqI hf ss ss' rs rs' (IndexesOfSubseq ss rs)
    )


type HSubseq' :: forall k. HTyConK k -> [k] -> [k] -> Constraint
type HSubseq' hf ss rs = HSubseq hf ss ss rs rs


hsubseq :: forall ss ss' rs rs' hf f.
    HSubseq hf ss ss' rs rs'
    => Lens (hf f rs) (hf f rs') (hf f ss) (hf f ss')
hsubseq = hsubseqI  @hf @ss @ss' @rs @rs' @(IndexesOfSubseq ss rs)
{-# inline hsubseq #-}


hsubseq' :: forall ss rs hf f. HSubseq' hf ss rs => Lens' (hf f rs) (hf f ss)
hsubseq' = hsubseq
{-# inline hsubseq' #-}


testSubseqInstance :: forall (hf :: HTyConK Type).
    ( HMonoid hf
    , HSubseq' hf '[Int,Double] '[Int,Char,Double]
    , HSubseq hf '[Int,Double] '[] '[Int,Char,Double] '[Char]
    )
    => ()
testSubseqInstance = ()
  where
    _testSub :: hf Identity '[Int,Char,Double] -> hf Identity '[Int,Double]
    _testSub = view (hsubseq @'[Int,Double])

    _testSubInf (h :: hf Identity '[Int,Char,Double]) =
        view (hsubseq @'[Int,Double]) h

    _testDelete :: hf Identity '[Int,Char,Double] -> hf Identity '[Char]
    _testDelete hl =
        set (hsubseq @'[Int,Double]) (hempty @hf) hl

    _testDeleteInf (hl :: hf Identity '[Int,Char,Double]) =
        set (hsubseq @'[Int,Double]) (hempty @hf) hl


type HQuotientI :: forall {k}. HTyConK k -> [k] -> [k] -> [k] -> [Peano] -> Constraint

class HSubseqI hf ss '[] rs rs' is => HQuotientI hf ss rs rs' is where
    -- Isomorphism when ss' ~ '[]: splitting rs into ss and rs'
    --  view hsubseqI :: rs -> ss
    --  set hsubseqI HNil :: rs -> rs'
    --  view hsubseqSplitI = view hsubseqI &&& set hsubseqI RNil
    --  rs is a permutation of ss ++ rs'
    hsubseqSplitI :: Iso' (hf f rs) (hf f ss, hf f rs')


type HQuotient :: forall {k}. HTyConK k -> [k] -> [k] -> [k] -> Constraint
type HQuotient hf sub rs q = HQuotientI hf sub rs q (IndexesOfSubseq sub rs)


hsubseqSplit :: forall ss rs rs' hf f.
    HQuotient hf ss rs rs'
    => Iso' (hf f rs) (hf f ss, hf f rs')
hsubseqSplit = hsubseqSplitI @hf @ss @rs @rs' @(IndexesOfSubseq ss rs)
{-# inline hsubseqSplit #-}

