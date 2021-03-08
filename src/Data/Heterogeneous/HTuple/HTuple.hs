{-# language AllowAmbiguousTypes #-}
{-# language QuantifiedConstraints #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
module Data.Heterogeneous.HTuple.HTuple where

import Control.Lens (Iso, iso)

import Data.Vinyl.XRec (IsoHKD)

import Data.Vinyl.Extra.Kind
import Data.Vinyl.Extra.TypeLevel


type TupleTyCon :: forall (n :: Nat) -> NAryTypeConK n Type Type
type family TupleTyCon n = t | t -> n


type TupleOf :: [Type] -> Type
newtype TupleOf as = Tuple (AppTyCon as (TupleTyCon (Length as)))


type HTuple :: forall k. HTyConK k
newtype HTuple f as = HTuple (TupleOf (Map f as))


type IsTupleOf :: [Type] -> Type -> Constraint
type IsTupleOf as t = AppliedTypeCon as (TupleTyCon (Length as))


type RTupled :: forall k. RecordKind k -> [k] -> Constraint

class RTupled rec as where
    rtupleWith :: forall f g tup_g_as.
        IsTupleOf (Map g as) tup_g_as
        => (forall a. f a -> g a)
        -> rec f as
        -> tup_g_as

    rtupleWithC :: forall c f g tup_g_as.
        ( FoldConstraints (Map c as)
        , IsTupleOf (Map g as) tup_g_as
        )
        => (forall a. c a => f a -> g a)
        -> rec f as
        -> tup_g_as

    rtupleHKDWith :: forall f g tup_g_as.
        ( forall a. IsoHKD g a
        , IsTupleOf (MapHKD g as) tup_g_as
        )
        => (forall a. f a -> g a)
        -> rec f as
        -> tup_g_as

    rtupleHKDWithC :: forall c f g tup_g_as.
        ( forall a. IsoHKD g a
        , FoldConstraints (Map c as)
        , IsTupleOf (MapHKD g as) tup_g_as
        )
        => (forall a. c a  => f a -> g a)
        -> rec f as
        -> tup_g_as


    fromRTuple :: forall f. RTupleOf f as -> rec f as

    fromRTupleHKD :: forall f. (forall a. IsoHKD f a) => RTupleHKDOf f as -> rec f as


rtuple :: (RTupled rec as, IsTupleOf (Map f as) t) => rec f as -> t
rtuple = rtupleWith id


rtupleHKD :: (RTupled rec as, IsTupleOf (MapHKD f as), forall a. IsoHKD f a) => rec f as -> t
rtupleHKD = rtupleHKDWith id


rtupled :: forall as bs rec f g t_as t_bs.
    ( RTupled rec as, IsTupleOf (Map f as) t_as
    , RTupled rec bs, IsTupleOf (Map g bs) t_bs
    )
    => Iso (rec f as) (rec g bs) t_as t_bs
rtupled = iso rtuple fromRTuple


rtupledHKD :: forall as bs rec f g.
    ( RTupled rec as, IsTupleOf (MapHKD f as) t_as
    , RTupled rec bs, IsTupleOf (MapHKD g bs) t_bs
    , forall a. IsoHKD f a
    , forall b. IsoHKD g b
    )
    => Iso (rec f as) (rec g bs) t_as t_bs
rtupledHKD = iso rtupleHKD fromRTupleHKD
