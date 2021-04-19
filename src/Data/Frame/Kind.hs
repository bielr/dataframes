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

  , ZippedFields

  , RecK
  , SeriesK
  , FrameK
  ) where

import GHC.TypeLits       as Exports (Symbol, TypeError, ErrorMessage(..))
import Data.Kind          as Exports (Constraint, Type)
import Data.Type.Bool     as Exports
import Data.Type.Equality as Exports (type (==))
import Fcf.Core

import Data.Heterogeneous.TypeLevel


-- kinds

data FieldK = Symbol :⊳ Type

-- If we use different symbols (the ASCII one is more accessible) then GHC will
-- not use 'Data.Kind.:> in type errors if both are in scope!
type (:>) :: Symbol -> Type -> FieldK
type (:>) = '(:⊳)


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


type ZippedFields :: [Symbol] -> [Type] -> [FieldK] -> Constraint
type ZippedFields ss as cols =
    ( ZippedWith (:>) ss as cols
    , ss ~ FMap FieldNameExp @@ cols
    , as ~ FMap FieldTypeExp @@ cols
    )

type RecK = HTyConK FieldK

type SeriesK = FieldK -> Type
type FrameK = [FieldK] -> Type
