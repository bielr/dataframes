{-# language AllowAmbiguousTypes #-}
{-# language QuantifiedConstraints #-}
{-# language UndecidableInstances #-}
module Data.Frame.Kind
  ( module Exports
  , FieldK(..)
  , type (:>)
  , FieldName
  , FieldType

  , FieldsK
  , RecK
  , FrameK
  --, When
  --, Forbid
  ) where

import GHC.TypeLits       as Exports (Symbol, TypeError, ErrorMessage(..))
import Data.Kind          as Exports (Constraint, Type)
import Data.Type.Bool     as Exports
import Data.Type.Equality as Exports (type (==))


-- kinds

data FieldK = Symbol :> Type

type (:>) :: Symbol -> Type -> FieldK
type s :> t = s ':> t

type FieldName :: FieldK -> Symbol
type family FieldName col where
    FieldName (s :> _) = s

type FieldType :: FieldK -> Type
type family FieldType col where
    FieldType (_ :> t) = t


type FieldsK = [FieldK]
type RecK = (FieldK -> Type) -> FieldsK -> Type

type FrameK = FieldsK -> Type


-- type When :: Bool -> Constraint -> Constraint
-- type When b c = If b c (() :: Constraint)


-- type Forbid :: Bool -> Symbol -> Constraint
--
-- type family Forbid b msg where
--     Forbid 'True   msg = TypeError ('Text msg)
--     Forbid 'False  _   = ()
--
