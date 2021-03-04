module Data.Frame.Row where

import qualified Data.Vector as VB

import Data.Frame.Field (Field)
import Data.Frame.Internal.Repr
import Data.Frame.Kind
import Data.Indexer (Indexer)


type RowVector = VB.Vector

type Row rec = rec Field


type RowsRepF :: Repr -> Type -> Type

type family RowsRepF rep = f | f -> rep where
    RowsRepF 'Vec = RowVector
    RowsRepF 'Idx = Indexer
