{-# options_ghc -Wno-orphans #-}
module Data.Heterogeneous.Class.TupleView where

import Control.Lens (Iso, iso)

import Data.Heterogeneous.Class.HConv
import Data.Heterogeneous.Constraints
import Data.Heterogeneous.HTuple
import Data.Heterogeneous.TypeLevel


type TupleView :: forall {k}. HTyConK k -> [k] -> Constraint

class TupleView hf as where
    htupleWith :: forall f g.
        (forall a. f a -> g a)
        -> hf f as
        -> HTuple g as

    htupleWithC :: forall c f g tup_g_as.
        ( FoldConstraints (Map c as)
        , IsTupleOf (Map g as) tup_g_as
        )
        => (forall a. c a => f a -> g a)
        -> hf f as
        -> HTuple g as

    fromHTuple :: HTuple f as -> hf f as

    -- rtupleHKDWith :: forall f g tup_g_as.
    --     ( forall a. IsoHKD g a
    --     , IsTupleOf (MapHKD g as) tup_g_as
    --     )
    --     => (forall a. f a -> g a)
    --     -> rec f as
    --     -> tup_g_as

    -- rtupleHKDWithC :: forall c f g tup_g_as.
    --     ( forall a. IsoHKD g a
    --     , FoldConstraints (Map c as)
    --     , IsTupleOf (MapHKD g as) tup_g_as
    --     )
    --     => (forall a. c a  => f a -> g a)
    --     -> rec f as
    --     -> tup_g_as

    -- fromRTupleHKD :: forall f. (forall a. IsoHKD f a) => RTupleHKDOf f as -> rec f as


instance {-# incoherent #-} TupleView hf as => HConv hf HTuple as where
    hconv = htupleWith id

instance {-# incoherent #-} TupleView hf as => HConv HTuple hf as where
    hconv = fromHTuple

-- htuple :: TupleView hf as => hf f as -> HTuple f as
-- htuple = htupleWith id


-- htupleHKD :: (RTupled rec as, IsTupleOf (MapHKD f as), forall a. IsoHKD f a) => rec f as -> t
-- htupleHKD = rtupleHKDWith id


htupled :: forall as bs hf f g.
    (TupleView hf as, TupleView hf bs)
    => Iso (hf f as) (hf g bs) (HTuple f as) (HTuple g bs)
htupled = iso hconv hconv


-- rtupledHKD :: forall as bs rec f g.
--     ( RTupled rec as, IsTupleOf (MapHKD f as) t_as
--     , RTupled rec bs, IsTupleOf (MapHKD g bs) t_bs
--     , forall a. IsoHKD f a
--     , forall b. IsoHKD g b
--     )
--     => Iso (rec f as) (rec g bs) t_as t_bs
-- rtupledHKD = iso rtupleHKD fromRTupleHKD
