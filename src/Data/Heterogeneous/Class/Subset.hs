{-# language AllowAmbiguousTypes #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.Class.Subset
  ( HSubsetI
  , HSubset
  , HReorder
  , hgetSubset
  , hsetSubset
  , hsubset
  , hreorder
  , hreordered
  ) where

import Control.Lens (Lens, Iso, lens, iso)

import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.TypeLevel.Subset (IsSubsetWithError)


type HSubsetI :: forall {k}. HTyConK k -> [k] -> [k] -> [Peano] -> Constraint

class IndexAll rs is ~ ss => HSubsetI hf ss rs is where
    hgetSubsetC :: hf f rs -> hf f ss
    hsetSubsetC :: hf f ss' -> hf f rs -> hf f rs

    hsubsetC :: Lens (hf f rs) (hf f rs) (hf f ss) (hf f ss)
    hsubsetC = lens (hgetSubsetC @hf @ss @rs @is) (flip (hsetSubsetC @hf @ss @rs @is))


type HSubset :: forall k. HTyConK k -> [k] -> [k] -> Constraint
type HSubset hf ss rs =
    ( IsSubsetWithError ss rs
    , HSubsetI hf ss rs (IndexesOf ss rs)
    )


type HReorder :: forall k. HTyConK k -> [k] -> [k] -> Constraint
type HReorder hf ss rs = (HSubset hf ss rs, HSubset hf rs ss)


hgetSubset :: forall ss rs hf f.
    HSubset hf ss rs
    => hf f rs -> hf f ss
hgetSubset = hgetSubsetC @hf @ss @rs @(IndexesOf ss rs)


hsetSubset :: forall ss rs hf f. HSubset hf ss rs => hf f ss -> hf f rs -> hf f rs
hsetSubset = hsetSubsetC @hf @ss @rs @(IndexesOf ss rs)


hsubset :: forall ss rs hf f.
    HSubset hf ss rs
    => Lens (hf f rs) (hf f rs) (hf f ss) (hf f ss)
hsubset = hsubsetC @hf @ss @rs @(IndexesOf ss rs)


hreorder :: forall ss rs hf f. (HSubset hf ss rs, HSubset hf rs ss) => hf f rs -> hf f ss
hreorder = hgetSubset


hreordered :: forall ss rs hf f g.
    (HSubset hf ss rs, HSubset hf rs ss)
    => Iso (hf f rs) (hf g rs) (hf f ss) (hf g ss)
hreordered = iso hreorder hreorder
