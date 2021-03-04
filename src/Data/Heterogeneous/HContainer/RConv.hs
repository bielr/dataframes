{-# language UndecidableInstances #-}
module Data.Heterogeneous.RConv where

import GHC.Exts (Any)

import Control.Lens (view)

import qualified Data.Primitive.SmallArray as SA

import Data.Vinyl (Rec(..))
import Data.Vinyl qualified as Vy
import Data.Vinyl.ARec (ARec, fromARec, toARec, IndexableField)
import Data.Vinyl.TypeLevel

import Unsafe.Coerce (unsafeCoerce)

import Data.Heterogeneous.RIxed
import Data.Heterogeneous.RNew
import Data.Vinyl.Extra.SARec (SARec(..))


-- Conversion between record types

class RConv rec rec' as where
    rconv :: forall f. rec f as -> rec' f as


instance NatToInt (RLength as) => RConv Rec SARec as where
    rconv rec =
        SARec $ SA.smallArrayFromListN n (toAnys rec)
      where
        n = natToInt @(RLength as)

        toAnys :: Rec f bs -> [Any]
        toAnys RNil      = []
        toAnys (a :& as) = unsafeCoerce a : toAnys as
    {-# inline rconv #-}


instance {-# overlappable #-} (RIxed rec, RNew Rec as) => RConv rec Rec as where
    rconv rec = rinew (\i -> view (rix i) rec)
    {-# inline rconv #-}
