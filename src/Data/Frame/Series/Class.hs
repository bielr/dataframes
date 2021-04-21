{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
module Data.Frame.Series.Class where

import GHC.TypeLits (KnownSymbol)

import Control.Lens

import Data.Vector.Generic qualified as VG

import Data.Frame.Kind
import Data.Frame.Field
import Data.Indexer


type IsSeries :: SeriesK -> Constraint

class IsSeries series where
    type CompatibleDataType series :: Type -> Constraint

    seriesValues ::
        ( FieldName col ~ FieldName col'
        , CompatibleDataType series (FieldType col)
        , CompatibleDataType series (FieldType col')
        )
        => IndexedTraversal Int
            (series col)    (series col')
            (FieldType col) (FieldType col')

    indexSeries ::
        CompatibleDataType series (FieldType col)
        => series col
        -> Indexer (FieldType col)

    seriesToVector ::
        ( CompatibleDataType series (FieldType col)
        , VG.Vector v (FieldType col)
        )
        => series col
        -> v (FieldType col)
    seriesToVector = copyIndexer . indexSeries


seriesLength ::
    ( IsSeries series
    , CompatibleDataType series (FieldType col)
    )
    => series col
    -> Int
seriesLength = length . indexSeries


class (IsSeries series, Monad m) => GenerateSeries m series where
    generateSeriesM ::
        CompatibleDataType series (FieldType col)
        => Indexer (m (FieldType col))
        -> m (series col)

    vectorToSeries ::
        ( CompatibleDataType series (FieldType col)
        , VG.Vector v (FieldType col)
        )
        => v (FieldType col)
        -> m (series col)
    vectorToSeries = generateSeriesM . fmap return . indexVector


generateSeries ::
    ( GenerateSeries Identity series
    , CompatibleDataType series (FieldType col)
    )
    => Indexer (FieldType col)
    -> series col
generateSeries idx = runIdentity $ generateSeriesM (Identity <$> idx)


class IsSeries series => TraversableSeries series where
    traverseSeries ::
        ( CompatibleDataType series (FieldType col)
        , CompatibleDataType series (FieldType col')
        )
        => Traversal (series col) (series col') (FieldType col) (FieldType col')



type CompatibleField :: SeriesK -> FieldK -> Constraint

class
    ( col ~ (FieldName col :> FieldType col)
    , KnownSymbol (FieldName col)
    , CompatibleDataType series (FieldType col)
    )
    => CompatibleField series col

instance
    ( col ~ (FieldName col :> FieldType col)
    , KnownSymbol (FieldName col)
    , CompatibleDataType series (FieldType col)
    )
    => CompatibleField series col


seriesFields ::
    ( IsSeries series
    , FieldName col ~ FieldName col'
    , CompatibleDataType series (FieldType col)
    , CompatibleDataType series (FieldType col')
    )
    => IndexedTraversal Int
        (series col) (series col')
        (Field col)  (Field col')
seriesFields = seriesValues.coerced


seriesIndexer ::
    ( GenerateSeries Identity series
    , FieldName col ~ FieldName col'
    , CompatibleDataType series (FieldType col)
    , CompatibleDataType series (FieldType col')
    )
    => Iso
        (series col)              (series col')
        (Indexer (FieldType col)) (Indexer (FieldType col'))
seriesIndexer = iso indexSeries generateSeries


seriesVector ::
    ( GenerateSeries Identity series
    , FieldName col ~ FieldName col'

    , CompatibleDataType series (FieldType col)
    , VG.Vector v (FieldType col)

    , CompatibleDataType series (FieldType col')
    , VG.Vector w (FieldType col')
    )
    => Iso
        (series col)        (series col')
        (v (FieldType col)) (w (FieldType col'))
seriesVector = iso seriesToVector (runIdentity . vectorToSeries)
