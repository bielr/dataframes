module Control.Lens.LazyTraversal
  ( -- re-exports
    Contravariant(..)
  , Distributive(..)
  , DistributiveFoldable(..)

  , LazyTraversal
  , IndexedLazyTraversal
  , IndexPreservingLazyTraversal

  , LazyTraversal'
  , IndexedLazyTraversal'
  , IndexPreservingLazyTraversal'

  , foldMapped
  , ifoldMapped
  , foldMapping

  -- conversions to lens
  , asFold
  , asSetter
  ) where

import Control.Comonad
import Control.Lens.Indexed
import Control.Lens.Type

import Data.Distributive
import Data.DistributiveFoldable
import Data.Functor.Contravariant
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Data.Profunctor.Unsafe


type LazyTraversal s t a b =
    forall f. (Applicative f, DistributiveFoldable f) => (a -> f b) -> s -> f t

type IndexedLazyTraversal i s t a b =
    forall p f. (Indexable i p, Applicative f, DistributiveFoldable f) => p a (f b) -> s -> f t

type IndexPreservingLazyTraversal s t a b =
    forall p f. (Conjoined p, Applicative f, DistributiveFoldable f) => p a (f b) -> p s (f t)


type LazyTraversal' s a = Simple LazyTraversal s a
type IndexedLazyTraversal' i s a = Simple (IndexedLazyTraversal i) s a
type IndexPreservingLazyTraversal' s a = Simple IndexPreservingLazyTraversal s a


foldMapped :: (Functor t, Foldable t) => LazyTraversal (t a) (t b) a b
foldMapped = foldCollect
{-# inline foldMapped #-}


ifoldMapped :: (FunctorWithIndex i t, Foldable t) => IndexedLazyTraversal i (t a) (t b) a b
ifoldMapped = conjoined foldMapped \f ta -> foldDistribute (imap (indexed f) ta)
{-# inline ifoldMapped #-}


foldMapping :: (Functor t, Foldable t) => IndexPreservingLazyTraversal (t a) (t b) a b
foldMapping pafb = cotabulate \ws -> foldMapped (\a -> cosieve pafb (a <$ ws)) (extract ws)
{-# inline foldMapping #-}


-- LazyTraversal to Fold
asFold ::
    (Profunctor p, Profunctor q, Contravariant f, Applicative f)
    => Optical p q (WrappedBivariant f) s t a b
    -> Optical p q f s t a b
asFold l pafb = unwrapBivariant #. l (WrappedBivariant #. pafb)
{-# inline asFold #-}


-- LazyTraversal to Setter
asSetter ::
    (Profunctor p, Profunctor q, Distributive f)
    => Optical p q (WrappedDistributive f) s t a b
    -> Optical p q f s t a b
asSetter l pafb = unwrapDistributive #. l (WrappedDistributive #. pafb)
{-# inline asSetter #-}
