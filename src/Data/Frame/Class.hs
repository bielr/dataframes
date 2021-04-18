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
    -- Env must be an Applicative functor
    , forall cols. Applicative (Env df cols)
    -- Env df cols must have a representational argument
    , forall cols a b. Coercible a b => Coercible (Env df cols a) (Env df cols b)
    )
    => IsFrame df where

    frameLength :: df cols -> Int

    type Column df :: FieldK -> Type

    data Env df :: [FieldK] -> Type -> Type

    withFrame :: (df cols -> r) -> Env df cols r
    getRowIndex :: Env df cols Int

    runEnv :: df cols -> Env df cols a -> Indexer a


frameEnvCo :: IsFrame df => (a :~>: b) -> (Env df cols a :~>: Env df cols b)
frameEnvCo Coercion = Coercion


htupleEnvCo :: forall t f df cols cols'.
    ( IsFrame df
    , HCoerce HTuple cols'
    , IsTupleOfF f cols' t
    )
    => Env df cols t :~>: Env df cols (HTuple f cols')
htupleEnvCo =
    frameEnvCo (hIdLCo . hconOutCo . htupleCo)


coerceHTupleEnv :: forall f cols' cols t df.
    ( IsFrame df
    , HCoerce HTuple cols'
    , IsTupleOfF f cols' t
    )
    => Env df cols t
    -> Env df cols (HTuple f cols')
coerceHTupleEnv = coerceWith htupleEnvCo


class
    ( IsFrame df
    , (cols !! i) ~ col
    )
    => HasColumn df col cols i where

    findColumn :: IsFieldsProxy cols i proxy => proxy -> df cols -> Column df col

    findField :: IsFieldsProxy cols i proxy => proxy -> Env df cols (Field col)


    default findColumn ::
        ( IsFieldsProxy cols i proxy
        , ColumnarFrame df hf cols
        , HGetI hf col cols i
        )
        => proxy
        -> df cols
        -> Column df col
    findColumn _ = hgetI @_ @_ @_ @i . toCols


    default findField ::
        ( IsFieldsProxy cols i proxy
        , CompatibleField (Column df) col
        )
        => proxy
        -> Env df cols (Field col)
    findField proxy =
        elemAt
            <$> withFrame (fmap Field #. indexSeries . findColumn proxy)
            <*> getRowIndex


class IsFrame df => ColumnarFrame df hf cols | df -> hf where
    toCols :: df cols -> hf (Column df) cols


class IsFrame df => FromSingleColumn df where
    fromSingleCol ::
        CompatibleDataType (Column df) (FieldType col)
        => Column df col
        -> df '[col]


class IsFrame df => ConcatCols df where
    unsafeConcatCols :: df cols -> df cols' -> df (cols ++ cols')


class IsFrame df => AppendCol df where
    appendCol ::
        CompatibleDataType (Column df) (FieldType col)
        => Env df cols (Field col)
        -> df cols
        -> df (cols ++ '[col])

    prependCol ::
        CompatibleDataType (Column df) (FieldType col)
        => Env df cols (Field col)
        -> df cols
        -> df (col ': cols)

    default appendCol :: forall col cols.
        ( FromSingleColumn df
        , ConcatCols df
        , GenerateSeries (Column df)
        , CompatibleDataType (Column df) (FieldType col)
        )
        => Env df cols (Field col)
        -> df cols
        -> df (cols ++ '[col])
    appendCol env df =
        unsafeConcatCols df (fromSingleCol newCol)
      where
        newCol = generateSeries @_ @col $ fmap getField (runEnv df env)


    default prependCol :: forall col cols.
        ( FromSingleColumn df
        , ConcatCols df
        , GenerateSeries (Column df)
        , CompatibleDataType (Column df) (FieldType col)
        )
        => Env df cols (Field col)
        -> df cols
        -> df (col ': cols)
    prependCol env df =
        unsafeConcatCols (fromSingleCol newCol) df
      where
        newCol = generateSeries @_ @col $ fmap getField (runEnv df env)


class (IsFrame df, GenerateSeries (Column df)) => GenerateFrame df hf cols where
    generateFrame :: CompatibleFields df cols => Indexer (hf Field cols) -> df cols


-- record :: forall ss as cols.
--     ( cols ~ ZipWith (:>) ss as
--     , Coercible (TupleOf as) (HTuple Field cols)
--     )
--     => TupleOf as
--     -> HTuple Field cols
-- record = coerce
