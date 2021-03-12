{-# language MagicHash #-}
{-# language UndecidableInstances #-}
module Data.Frame.TypeIndex where

import GHC.OverloadedLabels (IsLabel(..))
import GHC.Tuple
import Data.Heterogeneous.HTuple
import Data.Heterogeneous.TypeLevel.List
import Data.Frame.Kind


type FindField :: Symbol -> FieldsK -> FieldK
type family FindField s rs where
    FindField s ((s :> a) ': rs) = s :> a
    FindField s (r ': rs)        = FindField s rs


type FindFieldType :: Symbol -> FieldsK -> Type
type FindFieldType s rs = FieldType (FindField s rs)


-- type-level polymorphic field indexers

-- Specifying one or more field(s) by name(s) or full spec(s)
-- Polymorphic on both spec and result list-ness

type ProjField :: forall (ki :: Type) -> forall (kr :: Type) -> FieldsK -> ki -> kr

type family ProjField (ki :: Type) (kr :: Type) (rs :: FieldsK) (i :: ki) :: kr where
    ProjField FieldK  FieldK  rs  (s :> a)  = s :> a
    ProjField Symbol  FieldK  rs  s         = FindField s rs
    ProjField FieldK  Symbol  rs  (s :> a)  = s
    ProjField Symbol  Symbol  rs  s         = s
    ProjField FieldK  [kr]    rs  (s :> a)  = ProjField [FieldK] [kr] rs '[s :> a]
    ProjField Symbol  [kr]    rs  s         = ProjField [Symbol] [kr] rs '[s]
    ProjField [k]     [k]     rs  r         = r
    ProjField [ki]    [kr]    rs  '[]       = '[]
    ProjField [ki]    [kr]    rs  (i ': is) = ProjField ki kr rs i ': ProjField [ki] [kr] rs is


type FieldSpec :: forall ki kr. FieldsK -> ki -> kr -> Constraint
type FieldSpec rs (i :: ki) (r :: kr) = ProjField ki kr rs i ~ r


type SingleFieldProxy :: forall ki. ki -> Type
data SingleFieldProxy i = SingleFieldProxy

instance s ~ i => IsLabel s (SingleFieldProxy i) where
    fromLabel = SingleFieldProxy

instance s ~ i => IsLabel s (Solo (SingleFieldProxy i)) where
    fromLabel = Solo SingleFieldProxy


type family InferIndexKind kr where
    InferIndexKind FieldK   = Symbol
    InferIndexKind [FieldK] = [Symbol]

type FieldSpecProxy :: forall kr. kr -> FieldsK -> InferIndexKind kr -> Type -> Constraint
type family FieldSpecProxy r rs is proxy where
    FieldSpecProxy (r :: FieldK)   rs i  proxy = (FieldSpec rs i r, proxy ~ SingleFieldProxy i)
    FieldSpecProxy (r :: [FieldK]) rs is proxy = (FieldSpec rs is r, Mapped SingleFieldProxy is (TupleMembers proxy))


TODO: allow specifying r manually or by Int index
TODO: get rid of the `is` parameter (UnMap)


-- Specifying one or more field(s) by name(s) or full spec(s)
-- The list-ness of the spec determines the list-ness of the output

type InferFieldKind :: Type -> Type

type family InferFieldKind (ki :: Type) = (kr :: Type) where
    InferFieldKind [ki] = [InferFieldKind ki]
    InferFieldKind ki   = FieldK


type MonoFieldSpec :: forall ki kr. FieldsK -> ki -> kr -> Constraint
type MonoFieldSpec rs (i :: ki) (r :: kr) = (InferFieldKind ki ~ kr, ProjField ki kr rs i ~ r)


-- Specifying one or more field name(s) by name(s) or full spec(s)
-- Polymorphic on both spec and result list-ness

type ProjName :: forall (ki :: Type) -> forall (kr :: Type) -> ki -> kr

type family ProjName (ki :: Type) (kr :: Type) (i :: ki) :: kr where
    ProjName Symbol          Symbol s         = s
    ProjName (Symbol, Type)  Symbol '(s, a)   = s
    ProjName (Symbol, Type) [kr]    i         = ProjName [(Symbol, Type)] [kr] '[i]
    ProjName Symbol         [kr]    i         = ProjName [Symbol]         [kr] '[i]
    ProjName [k]            [k]     is        = is
    ProjName [ki]           [kr]    '[]       = '[]
    ProjName [ki]           [kr]    (i ': is) = ProjName ki kr i ': ProjName [ki] [kr] is


type NameSpec :: forall ki kr. ki -> kr -> Constraint
type NameSpec (i :: ki) (s :: kr) = ProjName ki kr i ~ s


type SingleNameProxy :: Symbol -> Type
data SingleNameProxy s = SingleNameProxy

instance s ~ i => IsLabel s (SingleNameProxy i) where
    fromLabel = SingleNameProxy

instance s ~ i => IsLabel s (Solo (SingleNameProxy i)) where
    fromLabel = Solo SingleNameProxy


type NameSpecProxy :: forall {ks}. ks -> Type -> Constraint
type family NameSpecProxy ss proxy where
    NameSpecProxy (s :: Symbol)    proxy = proxy ~ SingleNameProxy s
    NameSpecProxy (ss :: [Symbol]) proxy = Mapped SingleNameProxy ss (TupleMembers proxy)
