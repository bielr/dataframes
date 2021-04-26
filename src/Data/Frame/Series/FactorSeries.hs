module Data.Frame.Series.FactorSeries where

import Data.Frame.DataTypes.Factor
import Data.Frame.Kind
import Data.Frame.Series.Class
import Data.Heterogeneous.Constraints


newtype FactorSeries col = FactorSeries (Factor (FieldType col))


instance IsSeries FactorSeries where
    type CompatibleDataType FactorSeries = TrueC

    indexSeries (FactorSeries f) = indexFactor f
