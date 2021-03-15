{-# language AllowAmbiguousTypes #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
module Data.Frame.TypeIndex where

import GHC.OverloadedLabels (IsLabel(..))
import Data.Heterogeneous.HTuple
import Data.Heterogeneous.TypeLevel
import Data.Frame.Kind
import Type.Errors


type FindFieldIndexByName :: Symbol -> FieldsK -> Peano
type family FindFieldIndexByName s rs where
    FindFieldIndexByName s ((s :> a) ': _) = 'Zero
    FindFieldIndexByName s (r ': rs)       = 'Succ (FindFieldIndexByName s rs)


type FindFieldIndexByNameError :: Symbol -> FieldsK -> ErrorMessage
type FindFieldIndexByNameError s rs =
    'Text "Could not find field named "
    ':<>: 'ShowType s
    ':<>: 'Text " in "
    ':<>: 'ShowType rs


type FindFieldIndex :: Symbol -> FieldsK -> Peano
type family FindFieldIndex s rs where
    FindFieldIndex s ((s :> a) ': rs) = 'Zero
    FindFieldIndex s (r ': rs)        = 'Succ (FindFieldIndex s rs)


type FindFieldIndexError :: FieldK -> FieldsK -> ErrorMessage
type FindFieldIndexError r rs =
    'Text "Could not find field "
    ':<>: 'ShowType r
    ':<>: 'Text " in "
    ':<>: 'ShowType rs

-- type FindFieldType :: Symbol -> FieldsK -> Type
-- type FindFieldType s rs = FieldType (FindField s rs)


-- type-level polymorphic field indexers

-- Specifying one or more field(s) by name(s) or full spec(s)
-- Polymorphic on both spec and result list-ness

-- type ProjField :: forall (ki :: Type) -> forall (kr :: Type) -> FieldsK -> ki -> kr
--
-- type family ProjField (ki :: Type) (kr :: Type) (rs :: FieldsK) (i :: ki) :: kr where
--     ProjField FieldK  FieldK  rs  (s :> a)  = s :> a
--     ProjField Symbol  FieldK  rs  s         = FindField s rs
--     ProjField FieldK  Symbol  rs  (s :> a)  = s
--     ProjField Symbol  Symbol  rs  s         = s
--     ProjField FieldK  [kr]    rs  (s :> a)  = ProjField [FieldK] [kr] rs '[s :> a]
--     ProjField Symbol  [kr]    rs  s         = ProjField [Symbol] [kr] rs '[s]
--     ProjField [k]     [k]     rs  r         = r
--     ProjField [ki]    [kr]    rs  '[]       = '[]
--     ProjField [ki]    [kr]    rs  (i ': is) = ProjField ki kr rs i ': ProjField [ki] [kr] rs is
--
--
-- type FieldSpec :: forall ki kr. FieldsK -> ki -> kr -> Constraint
-- type FieldSpec rs (i :: ki) (r :: kr) = ProjField ki kr rs i ~ r


type FieldProxy :: FieldsK -> Peano -> Type
data FieldProxy rs i = FieldProxy


fieldSpec :: forall r i rs.
    IfStuck (ForcePeano (FindFieldIndexByName r rs))
        (DelayError (FindFieldIndexByNameError r rs))
        (Pure (i ~ FindFieldIndex r rs))
    => FieldProxy rs i
fieldSpec = FieldProxy


fieldNamed :: forall s i rs.
    IfStuck (ForcePeano (FindFieldIndexByName s rs))
        (DelayError (FindFieldIndexByNameError s rs))
        (Pure (i ~ FindFieldIndexByName s rs))
    => FieldProxy rs i
fieldNamed = FieldProxy


fieldAt :: forall i rs. FieldProxy rs i
fieldAt = FieldProxy


instance
    IfStuck (ForcePeano (FindFieldIndexByName s rs))
        (DelayError (FindFieldIndexByNameError s rs))
        (Pure (i ~ FindFieldIndexByName s rs))
    => IsLabel s (FieldProxy rs i) where
    fromLabel = FieldProxy


type EnsureFieldIndexProxies :: forall ki. FieldsK -> ki -> [Type] -> Constraint
type family EnsureFieldIndexProxies rs is proxies where
    EnsureFieldIndexProxies rs (i :: Peano)    proxies = proxies ~ '[FieldProxy rs i]
    EnsureFieldIndexProxies rs (is :: [Peano]) proxies = Mapped (FieldProxy rs) is proxies


type DesugarFieldProxyTuple :: ki -> Type -> [Type]
type family DesugarFieldProxyTuple ki proxy where
    DesugarFieldProxyTuple Peano   proxy             = '[proxy]
    DesugarFieldProxyTuple [Peano] (t -> (proxy, t)) = '[proxy]
    DesugarFieldProxyTuple [Peano] proxy             = TupleMembers proxy


type IsFieldsProxy :: forall {ki}. FieldsK -> ki -> Type -> Constraint

class EnsureFieldIndexProxies rs is (DesugarFieldProxyTuple ki proxy)
    => IsFieldsProxy rs (is :: ki) proxy
        | rs ki proxy -> is

instance proxy ~ FieldProxy rs i
    => IsFieldsProxy rs (i :: Peano) proxy

instance
    ( WhenStuck (DesugarFieldProxyTuple [Peano] proxy)
        (DelayError
            ('Text "Unable to desugar "
              ':<>: 'ShowType proxy
              ':<>: 'Text " into a spec for a list of fields. Have you tried using -XTupleSections syntax?"))
    , Mapped (FieldProxy rs) is (DesugarFieldProxyTuple [Peano] proxy)
    )
    => IsFieldsProxy rs (is :: [Peano]) proxy



-- type IsFieldsProxy :: forall kr. FieldsK -> kr -> Type -> Constraint
-- type IsFieldsProxy rs r proxy =
--     IsFieldSpecProxy_ rs r proxy
    -- IfStuck (IsFieldSpecProxy_ rs r proxy)
    --     (DelayError ('Text "oops"))
    --     (Pure (IsFieldSpecProxy_ rs r proxy))

-- TODO: allow specifying r manually or by Int index


-- Specifying one or more field(s) by name(s) or full spec(s)
-- The list-ness of the spec determines the list-ness of the output

-- type InferFieldKind :: Type -> Type
--
-- type family InferFieldKind (ki :: Type) = (kr :: Type) where
--     InferFieldKind [ki] = [InferFieldKind ki]
--     InferFieldKind ki   = FieldK
--
--
-- type MonoFieldSpec :: forall ki kr. FieldsK -> ki -> kr -> Constraint
-- type MonoFieldSpec rs (i :: ki) (r :: kr) = (InferFieldKind ki ~ kr, ProjField ki kr rs i ~ r)


-- Specifying one or more field name(s) by name(s) or full spec(s)
-- Polymorphic on both spec and result list-ness

-- type ProjName :: forall (ki :: Type) -> forall (kr :: Type) -> ki -> kr
--
-- type family ProjName (ki :: Type) (kr :: Type) (i :: ki) :: kr where
--     ProjName Symbol          Symbol s         = s
--     ProjName (Symbol, Type)  Symbol '(s, a)   = s
--     ProjName (Symbol, Type) [kr]    i         = ProjName [(Symbol, Type)] [kr] '[i]
--     ProjName Symbol         [kr]    i         = ProjName [Symbol]         [kr] '[i]
--     ProjName [k]            [k]     is        = is
--     ProjName [ki]           [kr]    '[]       = '[]
--     ProjName [ki]           [kr]    (i ': is) = ProjName ki kr i ': ProjName [ki] [kr] is
--
--
-- type NameSpec :: forall ki kr. ki -> kr -> Constraint
-- type NameSpec (i :: ki) (s :: kr) = ProjName ki kr i ~ s


type NameProxy :: Symbol -> Type
data NameProxy s = NameProxy


asName :: forall s. NameProxy s
asName = NameProxy


instance s ~ i => IsLabel s (NameProxy i) where
    fromLabel = NameProxy


type EnsureNameProxies :: forall ks. ks -> [Type] -> Constraint
type family EnsureNameProxies ss proxies where
    EnsureNameProxies (s :: Symbol)    proxies = proxies ~ '[NameProxy s]
    EnsureNameProxies (ss :: [Symbol]) proxies = Mapped NameProxy ss proxies


type DesugarNameProxyTuple :: ks -> Type -> [Type]
type family DesugarNameProxyTuple ks proxy where
    DesugarNameProxyTuple Symbol   proxy             = '[proxy]
    DesugarNameProxyTuple [Symbol] (t -> (proxy, t)) = '[proxy]
    DesugarNameProxyTuple [Symbol] proxy             = TupleMembers proxy


type IsNameProxy :: forall {ks}. ks -> Type -> Constraint

class
    EnsureNameProxies ss (DesugarNameProxyTuple ks proxy)
    => IsNameProxy (ss :: ks) proxy
        | ks proxy -> ss

instance
    proxy ~ NameProxy s
    => IsNameProxy (s :: Symbol) proxy

instance
    ( WhenStuck (DesugarFieldProxyTuple [Peano] proxy)
        (DelayError
            ('Text "Unable to desugar "
              ':<>: 'ShowType proxy
              ':<>: 'Text " into a spec for a list of names. Have you tried using -XTupleSections syntax?"))
    , Mapped NameProxy ss (DesugarNameProxyTuple [Symbol] proxy)
    )
    => IsNameProxy (ss :: [Symbol]) proxy
