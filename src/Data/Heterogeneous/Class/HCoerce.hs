{-# language AllowAmbiguousTypes #-}
{-# language MagicHash #-}
{-# language QuantifiedConstraints #-}
module Data.Heterogeneous.Class.HCoerce where

import GHC.Exts (Proxy#, proxy#)
import Data.Coerce
import Data.Type.Coercion

import Data.Heterogeneous.TypeLevel


type HCoerce :: forall {k1}. (forall k. HTyConK k) -> [k1] -> Constraint

type NatCoercion :: forall {k1} {k2}. (k1 -> Type) -> (k2 -> Type) -> (k1 -> Exp k2) -> Type
type NatCoercion f g h = forall a. Coercion (f a) (g (Eval (h a)))


class HCoerce (hf :: forall k. HTyConK k) (as :: [k1]) where
    hliftCoercion ::
        Coercion f g
        -> Coercion (hf f as) (hf g as)

    hliftCoercionF :: forall {k2} (f :: k1 -> Type) (g :: k2 -> Type) (h :: k1 -> Exp k2).
        Proxy# h
        -> NatCoercion f g h
        -> Coercion (hf f as) (hf g (Eval (FMap h as)))


hgcoerceWith :: forall (hf :: forall k. HTyConK k) as r f g.
    HCoerce hf as
    => Coercion f g
    -> (Coercible (hf f as) (hf g as) => r)
    -> r
hgcoerceWith co = gcoerceWith (hliftCoercion co)
{-# inline hgcoerceWith #-}


hcoerceWith :: forall f g (hf :: forall k. HTyConK k) as.
    HCoerce hf as
    => Coercion f g
    -> hf f as
    -> hf g as
hcoerceWith co = hgcoerceWith @hf @as co coerce
{-# inline hcoerceWith #-}


hgcoerceWithF :: forall (hf :: forall k. HTyConK k) as h r f g.
    HCoerce hf as
    => NatCoercion f g h
    -> (Coercible (hf f as) (hf g (Eval (FMap h as))) => r)
    -> r
hgcoerceWithF co = gcoerceWith (hliftCoercionF (proxy# @h) co)
{-# inline hgcoerceWithF #-}


hcoerceWithF :: forall h f g (hf :: forall k. HTyConK k) as.
    HCoerce hf as
    => NatCoercion f g h
    -> hf f as
    -> hf g (Eval (FMap h as))
hcoerceWithF co = hgcoerceWithF @hf @as @h co coerce
{-# inline hcoerceWithF #-}
