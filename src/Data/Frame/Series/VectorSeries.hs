{-# language GeneralizedNewtypeDeriving #-}
{-# language UndecidableInstances #-}
module Data.Frame.Series.VectorSeries
    ( VectorSeries(..)
    , MVectorSeries(..)
    , _VectorSeries
    , _MVectorSeries
    ) where

import GHC.Exts (IsList)
import Control.Lens

import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Lens

import Data.Indexer
import Data.Frame.Kind
import Data.Frame.DataTypes.Vector
import Data.Frame.Series.Class


class (VG.Vector Vector a, KnownVectorMode (VectorModeOf a)) => CompatibleDataType_ a
instance (VG.Vector Vector a, KnownVectorMode (VectorModeOf a)) => CompatibleDataType_ a


type VectorSeries :: FieldK -> Type
newtype VectorSeries col = VectorSeries (Vector (FieldType col))

deriving newtype instance IsList (Vector (FieldType col)) => IsList (VectorSeries col)


type MVectorSeries :: Type -> FieldK -> Type
newtype MVectorSeries s col = MVectorSeries (MVector s (FieldType col))


_VectorSeries ::
    FieldName col ~ FieldName col'
    => Iso (Vector (FieldType col)) (Vector (FieldType col')) (VectorSeries col) (VectorSeries col')
_VectorSeries = coerced


_MVectorSeries ::
    FieldName col ~ FieldName col'
    => Iso
        (MVector s (FieldType col)) (MVector s (FieldType col'))
        (MVectorSeries s col)       (MVectorSeries s col')
_MVectorSeries = coerced


instance IsSeries VectorSeries where
    type CompatibleDataType VectorSeries = CompatibleDataType_

    seriesValues = from _VectorSeries . vectorTraverse

    indexSeries (VectorSeries v) = indexVector v

    seriesToVector (VectorSeries v) = VG.convert v
{-# rules "seriesToVector/VectorSeries/coerce" seriesToVector = \(VectorSeries v) -> v #-}


instance GenerateSeries VectorSeries where
    generateSeries = VectorSeries . copyIndexer

    vectorToSeries = VectorSeries . VG.convert
{-# rules "vectorToSeries/VectorSeries/coerce" vectorToSeries = VectorSeries #-}
