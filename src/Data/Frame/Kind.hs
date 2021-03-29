{-# language AllowAmbiguousTypes #-}
{-# language QuantifiedConstraints #-}
{-# language UndecidableInstances #-}
module Data.Frame.Kind
  ( module Exports
  , FieldK(..)
  , type (:>)
  , FieldName
  , FieldType
  , FieldNameExp
  , FieldTypeExp

  , FieldsK
  , RecK
  , FrameK
  ) where

import GHC.TypeLits       as Exports (Symbol, TypeError, ErrorMessage(..))
import Data.Kind          as Exports (Constraint, Type)
import Data.Type.Bool     as Exports
import Data.Type.Equality as Exports (type (==))
import Fcf.Core


-- kinds

data FieldK = Symbol :> Type

type (:>) :: Symbol -> Type -> FieldK
type (:>) = '(:>)

type FieldName :: FieldK -> Symbol
type family FieldName col where
    FieldName (s :> _) = s

type FieldType :: FieldK -> Type
type family FieldType col where
    FieldType (_ :> t) = t


type FieldNameExp :: FieldK -> Exp Symbol
data FieldNameExp col :: Exp Symbol
type instance Eval (FieldNameExp col) = FieldName col

type FieldTypeExp :: FieldK -> Exp Type
data FieldTypeExp col :: Exp Type
type instance Eval (FieldTypeExp col) = FieldType col


type FieldsK = [FieldK]
type RecK = (FieldK -> Type) -> FieldsK -> Type

type FrameK = FieldsK -> Type
