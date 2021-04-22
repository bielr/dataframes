module Data.Frame.Series.FactorizedSeries where

import Data.Indexer
import Data.Vector qualified as VB

import Data.Frame.DataTypes.Factor
import Data.Frame.Kind
import Data.Frame.Series.Class
import Data.Heterogeneous.Constraints


newtype FactorizedSeries col =
    FactorizedSeries (FactorizedVector (FieldType col))


instance IsSeries FactorizedSeries where
    type CompatibleDataType FactorizedSeries = TrueC

    indexSeries (FactorizedSeries (FactorizedVector f is)) =
        let !labels = factorLabels f
        in
            VB.unsafeIndex labels <$> indexVector is

    seriesToVector = copyIndexer . indexSeries

