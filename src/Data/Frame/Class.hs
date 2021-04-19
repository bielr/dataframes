{-# language MagicHash #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
{-# language QuantifiedConstraints #-}
module Data.Frame.Class where

import Prelude hiding ((.))

import Control.Category (Category(..))
import Data.Coerce
import Data.Profunctor.Unsafe
import Data.Type.Coercion

import Data.Frame.Field
import Data.Frame.Kind
import Data.Frame.Series.Class
import Data.Frame.TypeIndex
import Data.Heterogeneous.Class.HCoerce
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.Constraints
import Data.Heterogeneous.HTuple
import Data.Heterogeneous.TypeLevel
import Data.Indexer


type CompatibleDataTypes :: FrameK -> [Type] -> Constraint
type CompatibleDataTypes df as = All (CompatibleDataType (Column df)) as


type CompatibleFields :: FrameK -> [FieldK] -> Constraint
type CompatibleFields df cols = All (CompatibleField (Column df)) cols


type IsFrame :: FrameK -> Constraint

class
    -- Columns should be some kind of series
    ( IsSeries (Column df)
    -- Eval must be an Applicative functor
    , forall cols. Applicative (Eval df cols)
    -- Eval df cols must have a representational argument
    , forall cols a b. Coercible a b => Coercible (Eval df cols a) (Eval df cols b)
    )
    => IsFrame df where

    frameLength :: df cols -> Int

    type Column df :: FieldK -> Type

    data Eval df :: [FieldK] -> Type -> Type

    withFrame :: (df cols -> r) -> Eval df cols r
    getRowIndex :: Eval df cols Int

    runEval :: df cols -> Eval df cols a -> Indexer a


frameEvalCo :: IsFrame df => (a :~>: b) -> (Eval df cols a :~>: Eval df cols b)
frameEvalCo Coercion = Coercion


htupleEvalCo :: forall t f df cols cols'.
    ( IsFrame df
    , HCoerce HTuple cols'
    , IsTupleOfF f cols' t
    )
    => Eval df cols t :~>: Eval df cols (HTuple f cols')
htupleEvalCo = frameEvalCo (hIdLCo . hconOutCo . htupleCo)


coerceHTupleEval :: forall f cols' cols t df.
    ( IsFrame df
    , HCoerce HTuple cols'
    , IsTupleOfF f cols' t
    )
    => Eval df cols t
    -> Eval df cols (HTuple f cols')
coerceHTupleEval = coerceWith htupleEvalCo


class IsFrame df => HasColumnAt df cols i where
    findColumn :: IsFieldsProxy cols i proxy => proxy -> df cols -> Column df (cols !! i)

    default findColumn ::
        ( IsFieldsProxy cols i proxy
        , ColumnarFrame df
        , HGetI (ColumnarHRep df) cols i
        )
        => proxy
        -> df cols
        -> Column df (cols !! i)
    findColumn _ = hgetI @_ @_ @i . toCols


class HasColumnAt df cols (IndexOf col cols) => HasColumn df cols col
instance HasColumnAt df cols (IndexOf col cols) => HasColumn df cols col


findField ::
    ( IsFieldsProxy cols i proxy
    , HasColumnAt df cols i
    , CompatibleField (Column df) (cols !! i)
    )
    => proxy
    -> Eval df cols (Field (cols !! i))
findField proxy =
    elemAt
        <$> withFrame (fmap Field #. indexSeries . findColumn proxy)
        <*> getRowIndex


class IsFrame df => ColumnarFrame df where
    type ColumnarHRep df :: RecK

    toCols :: df cols -> ColumnarHRep df (Column df) cols


class IsFrame df => FromSingleColumn df where
    fromSingleCol ::
        CompatibleDataType (Column df) (FieldType col)
        => Column df col
        -> df '[col]


class ColumnarFrame df => ConcatCols df where
    unsafeConcatCols :: df cols -> df cols' -> df (cols ++ cols')


class ColumnarFrame df => AppendCol df where
    appendCol ::
        CompatibleDataType (Column df) (FieldType col)
        => Eval df cols (Field col)
        -> df cols
        -> df (cols ++ '[col])

    prependCol ::
        CompatibleDataType (Column df) (FieldType col)
        => Eval df cols (Field col)
        -> df cols
        -> df (col ': cols)


    default appendCol :: forall col cols.
        ( FromSingleColumn df
        , ConcatCols df
        , GenerateSeries (Column df)
        , CompatibleDataType (Column df) (FieldType col)
        )
        => Eval df cols (Field col)
        -> df cols
        -> df (cols ++ '[col])
    appendCol ecol df =
        unsafeConcatCols df (fromSingleCol newCol)
      where
        newCol = generateSeries @_ @col $ fmap getField (runEval df ecol)


    default prependCol :: forall col cols.
        ( FromSingleColumn df
        , ConcatCols df
        , GenerateSeries (Column df)
        , CompatibleDataType (Column df) (FieldType col)
        )
        => Eval df cols (Field col)
        -> df cols
        -> df (col ': cols)
    prependCol ecol df =
        unsafeConcatCols (fromSingleCol newCol) df
      where
        newCol = generateSeries @_ @col $ fmap getField (runEval df ecol)


class (IsFrame df, GenerateSeries (Column df)) => GenerateFrame df hf cols where
    generateFrame :: CompatibleFields df cols => Indexer (hf Field cols) -> df cols
