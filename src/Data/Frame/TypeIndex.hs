{-# language AllowAmbiguousTypes #-}
{-# language MagicHash #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
module Data.Frame.TypeIndex where

import GHC.Exts (Proxy#, proxy#)
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


-- type-level polymorphic field indexers

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


ofFrame :: df rs -> FieldProxy rs i -> FieldProxy rs i
ofFrame _ = id


fieldProxy :: FieldProxy rs i -> Proxy# (rs !! i)
fieldProxy _ = proxy#


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

