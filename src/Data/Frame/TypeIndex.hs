{-# language UndecidableInstances #-}
module Data.Frame.TypeIndex where

import Data.Vinyl.Derived   as Vinyl (FieldType)

import Data.Frame.Kind


-- type-level polymorphic field indexers

-- Specifying one or more field(s) by name(s) or full spec(s)
-- Polymorphic on both spec and result list-ness

type ProjField :: forall ki -> forall kr -> FieldsK -> ki -> kr

type family ProjField (ki :: Type) (kr :: Type) (rs :: FieldsK) (i :: ki) :: kr where
    ProjField (Symbol, Type) (Symbol, Type)  rs  '(s, a)   = '(s, a)
    ProjField Symbol         (Symbol, Type)  rs  s         = '(s, FieldType s rs)
    ProjField (Symbol, Type) Symbol          rs  '(s, a)   = s
    ProjField Symbol         Symbol          rs  s         = s
    ProjField (Symbol, Type) [kr]            rs  '(s, a)   = ProjField [(Symbol, Type)] [kr] rs '[ '(s, a)]
    ProjField Symbol         [kr]            rs  s         = ProjField [Symbol]         [kr] rs '[s]
    ProjField [k]            [k]             rs  r         = r
    ProjField [ki]           [kr]            rs  '[]       = '[]
    ProjField [ki]           [kr]            rs  (i ': is) = ProjField ki kr rs i ': ProjField [ki] [kr] rs is


type FieldSpec :: forall ki kr. FieldsK -> ki -> kr -> Constraint
type FieldSpec rs (i :: ki) (r :: kr) = ProjField ki kr rs i ~ r


-- Specifying one or more field(s) by name(s) or full spec(s)
-- The list-ness of the spect determines the list-ness of the output

type InferFieldKind :: Type -> Type

type family InferFieldKind (ki :: Type) = (kr :: Type) where
    InferFieldKind [ki] = [InferFieldKind ki]
    InferFieldKind ki   = FieldK


type MonoFieldSpec :: forall ki kr. FieldsK -> ki -> kr -> Constraint
type MonoFieldSpec rs (i :: ki) (r :: kr) = (InferFieldKind ki ~ kr, ProjField ki kr rs i ~ r)


-- Specifying one or more field name(s) by name(s) or full spec(s)
-- Polymorphic on both spec and result list-ness

type ProjName :: forall ki -> forall kr -> ki -> kr

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
