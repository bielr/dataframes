{-# language UndecidableInstances #-}
module Data.Heterogeneous.RecSubset
  ( RecSubset
  , rsubset
  , rcast
  ) where

import Data.Vinyl (Rec(..))
import Data.Vinyl.ARec (ARec)
import Data.Vinyl qualified as Vy
import Data.Vinyl.TypeLevel

import Data.Vinyl.Extra.Kind
import Data.Vinyl.Extra.SARec (SARec)


type RecSubset :: forall k. RecordKind k -> [k] -> [k] -> Constraint

class Vy.RecSubset rec ss rs (RImage ss rs) => RecSubset rec ss rs where
    rsubsetC :: Functor g => (rec f ss -> g (rec f ss)) -> rec f rs -> g (rec f rs)

    rcastC :: rec f rs -> rec f ss


instance Vy.RecSubset Rec ss rs (RImage ss rs) => RecSubset Rec ss rs where
    rsubsetC = Vy.rsubsetC
    rcastC = Vy.rcastC


instance Vy.RecSubset ARec ss rs (RImage ss rs) => RecSubset ARec ss rs where
    rsubsetC = Vy.rsubsetC
    rcastC = Vy.rcastC


instance Vy.RecSubset SARec ss rs (RImage ss rs) => RecSubset SARec ss rs where
    rsubsetC = Vy.rsubsetC
    rcastC = Vy.rcastC


rsubset :: forall ss rs rec f g.
    (Functor g, RecSubset rec ss rs)
    => (rec f ss -> g (rec f ss))
    -> (rec f rs -> g (rec f rs))
rsubset = rsubsetC


rcast :: forall ss rs rec f.  RecSubset rec ss rs => rec f rs -> rec f ss
rcast = rcastC
