{-# language AllowAmbiguousTypes #-}
{-# language QuantifiedConstraints #-}
{-# language UndecidableInstances #-}
module Data.Frame.Kind
  ( module Exports
  , FieldK
  , FieldsK
  , RecK
  , FrameK
  , When
  , Forbid
  ) where

import GHC.TypeLits       as Exports (Symbol, TypeError, ErrorMessage(..))
import Data.Kind          as Exports (Constraint, Type)
import Data.Type.Bool     as Exports
import Data.Type.Equality as Exports (type (==))


-- kinds

type FieldK = (Symbol, Type)
type FieldsK = [FieldK]
type RecK = (FieldK -> Type) -> FieldsK -> Type

type FrameK = FieldsK -> Type


type When :: Bool -> Constraint -> Constraint
type When b c = If b c (() :: Constraint)


type Forbid :: Bool -> Symbol -> Constraint

type family Forbid b msg where
    Forbid 'True   msg = TypeError ('Text msg)
    Forbid 'False  _   = ()

