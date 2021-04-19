{-# language AllowAmbiguousTypes #-}
{-# language MagicHash #-}
{-# language QuantifiedConstraints #-}
module Data.Heterogeneous.Class.HCoerce where

import GHC.Exts (Proxy#, proxy#)
import Data.Coerce
import Data.Type.Coercion

import Data.Heterogeneous.Functors
import Data.Heterogeneous.TypeLevel


type HCoerce :: forall k. HPolyTyConK -> [k] -> Constraint


infix 4 :~>:

type (:~>:) :: Type -> Type -> Type
type (:~>:) = Coercion


type NatCoercion :: forall {k1} {k2}. (k1 -> Type) -> (k2 -> Type) -> (k1 -> Exp k2) -> Type
type NatCoercion f g h = forall a. f a :~>: g (h @@ a)


class HCoerce (hf :: HPolyTyConK) (as :: [k]) where
    hliftCo ::
        NatCoercion f g Pure
        -> hf f as :~>: hf g as

    hliftExpCo :: forall {k'} (f :: k -> Type) (g :: k' -> Type) (h :: k -> Exp k').
        Proxy# h
        -> NatCoercion f g h
        -> Coercion (hf f as) (hf g (FMap h @@ as))


hconInCo :: forall (hf :: HPolyTyConK) as fas f g.
    ( HCoerce hf as
    , Mapped f as fas
    , forall a b. Coercible a b => Coercible (g a) (g b)
    )
    => hf (g :. f) as :~>: hf g fas
hconInCo = hliftExpCo (proxy# @(Pure1 f)) Coercion
{-# inline hconInCo #-}


hconOutCo :: forall (hf :: HPolyTyConK) as fas f g.
    ( HCoerce hf as
    , Mapped f as fas
    , forall a b. Coercible a b => Coercible (g a) (g b)
    )
    => hf g fas :~>: hf (g :. f) as
hconOutCo = sym hconInCo
{-# inline hconOutCo #-}


hIdLCo :: forall (hf :: HPolyTyConK) as f.
    HCoerce hf as
    => hf (Identity :. f) as
    :~>: hf f as
hIdLCo = hliftCo Coercion
{-# inline hIdLCo #-}


hIdRCo :: forall (hf :: HPolyTyConK) as f.
    ( HCoerce hf as
    , forall a b. Coercible a b => Coercible (f a) (f b)
    )
    => hf (f :. Identity) as :~>: hf f as
hIdRCo = hliftCo Coercion
{-# inline hIdRCo #-}


hgcoerceWith :: forall (hf :: HPolyTyConK) as r f g.
    HCoerce hf as
    => NatCoercion f g Pure
    -> (Coercible (hf f as) (hf g as) => r)
    -> r
hgcoerceWith co = gcoerceWith (hliftCo co)
{-# inline hgcoerceWith #-}


hcoerceWith :: forall f g (hf :: HPolyTyConK) as.
    HCoerce hf as
    => NatCoercion f g Pure
    -> hf f as
    -> hf g as
hcoerceWith co = hgcoerceWith @hf @as co coerce
{-# inline hcoerceWith #-}


hgcoerceExpWith :: forall (hf :: HPolyTyConK) as h r f g.
    HCoerce hf as
    => NatCoercion f g h
    -> (Coercible (hf f as) (hf g (FMap h @@ as)) => r)
    -> r
hgcoerceExpWith co = gcoerceWith (hliftExpCo (proxy# @h) co)
{-# inline hgcoerceExpWith #-}


hcoerceExpWith :: forall h f g (hf :: HPolyTyConK) as.
    HCoerce hf as
    => NatCoercion f g h
    -> hf f as
    -> hf g (FMap h @@ as)
hcoerceExpWith co = hgcoerceExpWith @hf @as @h co coerce
{-# inline hcoerceExpWith #-}
