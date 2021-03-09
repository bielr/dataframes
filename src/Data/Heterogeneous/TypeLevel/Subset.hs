{-# language UndecidableInstances #-}
module Data.Heterogeneous.TypeLevel.Subset
  ( IsSet
  , IsSubset
  , IsSubsetWithError
  ) where

import Type.Errors

import Data.Heterogeneous.TypeLevel.Index
import Data.Heterogeneous.TypeLevel.Kind
import Data.Heterogeneous.TypeLevel.Peano



type DecreaseAll :: [Peano] -> [Peano]
type family DecreaseAll is where
    DecreaseAll '[]             = '[]
    DecreaseAll ('Succ i ': is) = i ': DecreaseAll is


type ForceDiagSeq :: [Peano] -> ()
type family ForceDiagSeq is where
    ForceDiagSeq '[]           = '()
    ForceDiagSeq ('Zero ': is) = ForceDiagSeq (DecreaseAll is)


type RepeatedElemsError :: forall k. [k] -> ErrorMessage
type RepeatedElemsError as =
    'Text "The type-level list"
    ':<>: 'ShowType as
    ':<>: 'Text " has repeated elements"


type IsSet :: forall k. [k] -> Constraint
type IsSet as =
    WhenStuck (ForceDiagSeq (IndexesOf as as))
        (DelayError (RepeatedElemsError as))


type IsSubset :: forall k. [k] -> [k] -> Constraint
type IsSubset ss rs = (IsSet ss, IsSet rs, AreIndexesOf (IndexesOf ss rs) ss rs)


type IsSubsetWithError :: forall k. [k] -> [k] -> Constraint
type IsSubsetWithError ss rs =
    ( IsSet ss
    , IsSet rs
    , AreIndexesOfWithError (IndexesOf ss rs) ss rs
    )
