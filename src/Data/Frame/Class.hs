{-# language MagicHash #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
{-# language QuantifiedConstraints #-}
module Data.Frame.Class where

import Prelude hiding ((.))

import Control.Category (Category(..))
import Control.Monad.Morph (MFunctor)
import Control.Lens.Type
import Data.Coerce
import Data.Functor.Apply
import Data.Functor.Identity
import Data.Profunctor.Unsafe
import Data.Roles
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
import Data.Heterogeneous.TypeLevel.Subseq


type CompatibleDataTypes :: FrameK -> [Type] -> Constraint
type CompatibleDataTypes df as = All (CompatibleDataType (Column df)) as


type CompatibleFields :: FrameK -> [FieldK] -> Constraint
type CompatibleFields df cols = All (CompatibleField (Column df)) cols


asCoercion :: Coercible a b => (a -> b) -> (a :~>: b)
asCoercion _ = Coercion


asTypeOfCo :: (a :~>: b) -> (a -> b) -> (a :~>: b)
asTypeOfCo = const


type IsFrame :: FrameK -> Constraint

class
    -- Columns should be some kind of series
    ( IsSeries (Column df)
    -- EvalT must be an Applicative functor
    , forall cols m. Apply m => Apply (EvalT df cols m)
    -- EvalT df cols m must have a representational argument
    , forall cols m. Representational m => Representational (EvalT df cols m)
    -- EvalT df cols must be a MFunctor
    , forall cols. MFunctor (EvalT df cols)
    )
    => IsFrame df where

    frameLength :: df cols -> Int

    type Column df :: FieldK -> Type

    data EvalT df :: [FieldK] -> (Type -> Type) -> Type -> Type

    withFrame :: Monad m => (df cols -> EvalT df cols m r) -> EvalT df cols m r
    getRowIndex :: Monad m => EvalT df cols m Int

    mapEvalM ::
        Monad m
        => (a -> m b)
        -> EvalT df cols m a
        -> EvalT df cols m b

    foldlEvalM ::
        Monad m
        => (b -> a -> m b)
        -> b
        -> df cols
        -> EvalT df cols m a
        -> m b

    sourceColumn ::
        Monad m
        => Column df col
        -> EvalT df cols m (Field col)

frameEvalCo ::
    ( IsFrame df
    , Representational m
    )
    => (a :~>: b)
    -> (EvalT df cols m a :~>: EvalT df cols m b)
frameEvalCo = rep


htupleEvalCo :: forall t f df cols cols' m.
    ( IsFrame df
    , HCoerce HTuple cols'
    , IsTupleOfF f cols' t
    , Representational m
    )
    => EvalT df cols m t :~>: EvalT df cols m (HTuple f cols')
htupleEvalCo = frameEvalCo htupleCoF


coerceHTupleEval :: forall f cols' cols t df m.
    ( IsFrame df
    , HCoerce HTuple cols'
    , IsTupleOfF f cols' t
    , Representational m
    )
    => EvalT df cols m t
    -> EvalT df cols m (HTuple f cols')
coerceHTupleEval = coerceWith htupleEvalCo


-- evalColumn :: forall col cols df.
--     ( IsFrame df
--     , GenerateSeries Identity (Column df)
--     , CompatibleDataType (Column df) (FieldType col)
--     )
--     => df cols
--     -> Eval df cols (FieldType col)
--     -> Column df col
-- evalColumn df = generateSeries . runEval df
--
--
-- evalColumnM :: forall col cols df m.
--     ( IsFrame df
--     , GenerateSeries m (Column df)
--     , CompatibleDataType (Column df) (FieldType col)
--     )
--     => df cols
--     -> Eval df cols (m (FieldType col))
--     -> m (Column df col)
-- evalColumnM df = generateSeriesM . runEval df


class IsFrame df => HasColumnAt df cols i where
    findColumn :: IsFieldsProxy cols i proxy => proxy -> df cols -> Column df (cols !! i)

    findField ::
        ( IsFieldsProxy cols i proxy
        , CompatibleField (Column df) (cols !! i)
        , Monad m
        )
        => proxy
        -> EvalT df cols m (Field (cols !! i))
    findField proxy = withFrame (sourceColumn . findColumn proxy)


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


class
    ( HasColumnAt df cols i
    , HasColumnAt df cols' i
    , TraversableSeries (Column df)
    , col' ~ FieldName col :> FieldType col'
    , ReplaceSubseqI '[col] '[col'] cols cols' '[i]
    )
    => HasColumnTraversal df col col' cols cols' i where

    columnValues ::
        ( IsFieldsProxy cols i proxy
        , CompatibleDataType (Column df) (FieldType col)
        , CompatibleDataType (Column df) (FieldType col')
        )
        => proxy
        -> IndexedTraversal Int
            (df cols)       (df cols')
            (FieldType col) (FieldType col')


class IsFrame df => ColumnarFrame df where
    type ColumnarHRep df :: RecK

    toCols :: df cols -> ColumnarHRep df (Column df) cols


class IsFrame df => ColumnarFrameEdit df where
    editColsWith ::
        (forall f. ColumnarHRep df f cols -> ColumnarHRep df f cols')
        -> df cols
        -> df cols'


    splitFrameWith ::
        (forall f.
            ColumnarHRep df f cols
            -> (ColumnarHRep df f cols', ColumnarHRep df f cols''))
        -> df cols
        -> (df cols', df cols'')
    splitFrameWith split df =
        ( editColsWith (fst . split) df
        , editColsWith (snd . split) df
        )


class IsFrame df => EmptyFrame df where
    emptyFrame :: Int -> df '[]


class ColumnarFrameEdit df => FrameMerge df where
    unsafeMergeFramesWith ::
        (forall f.
            ColumnarHRep df f cols
            -> ColumnarHRep df f cols'
            -> ColumnarHRep df f cols'')
        -> df cols
        -> df cols'
        -> df cols''


class (ColumnarFrameEdit df, GenerateSeries m (Column df)) => InsertColumn m df where
    insertColumnWithM ::
        CompatibleField (Column df) col
        => (forall f. ColumnarHRep df f cols -> f col -> ColumnarHRep df f cols')
        -> EvalT df cols m (Field col)
        -> df cols
        -> m (df cols')


insertColumnWith :: forall col df cols cols'.
    ( InsertColumn Identity df
    , CompatibleField (Column df) col
    )
    => (forall f. ColumnarHRep df f cols -> f col -> ColumnarHRep df f cols')
    -> EvalT df cols Identity (Field col)
    -> df cols
    -> df cols'
insertColumnWith insert =
    (runIdentity .) #. insertColumnWithM insert


class InsertColumn m df => ExtendFrame m df hf cols' where
    extendFrameWithM ::
        (forall f.
            ColumnarHRep df f cols
            -> ColumnarHRep df f cols'
            -> ColumnarHRep df f cols'')
        -> EvalT df cols m (hf Field cols')
        -> df cols
        -> m (df cols'')


extendFrameWith ::
    ExtendFrame Identity df hf cols'
    => (forall f.
            ColumnarHRep df f cols
            -> ColumnarHRep df f cols'
            -> ColumnarHRep df f cols'')
    -> EvalT df cols Identity (hf Field cols')
    -> df cols
    -> df cols''
extendFrameWith insert =
    (runIdentity .) #. extendFrameWithM insert


class ExtendFrame m df hf cols' => ExtendFrameMaybe m df hf cols cols' where
    extendFrameWithMaybeM ::
        (forall f.
            ColumnarHRep df f cols
            -> ColumnarHRep df f cols'
            -> ColumnarHRep df f cols'')
        -> EvalT df cols m (Maybe (hf Field cols'))
        -> df cols
        -> m (df cols'')


extendFrameWithMaybe ::
    ExtendFrameMaybe Identity df hf cols cols'
    => (forall f.
            ColumnarHRep df f cols
            -> ColumnarHRep df f cols'
            -> ColumnarHRep df f cols'')
    -> EvalT df cols Identity (Maybe (hf Field cols'))
    -> df cols
    -> df cols''
extendFrameWithMaybe insert =
    (runIdentity .) #. extendFrameWithMaybeM insert


{-
type GenerateFrame m df hf cols =
    ( EmptyFrame df
    , ExtendFrame m df hf cols
    )


generateFrameM :: forall df cols hf m.
    ( GenerateFrame m df hf cols
    , CompatibleFields df cols
    )
    => Indexer (m (hf Field cols))
    -> m (df cols)
generateFrameM (Indexer n imfield) =
    extendFrameWithM (\_ new -> new)
        (imfield <$> getRowIndex)
        (emptyFrame n)


generateFrame :: forall df cols hf.
    ( GenerateFrame Identity df hf cols
    , CompatibleFields df cols
    )
    => Indexer (hf Field cols)
    -> df cols
generateFrame =
    runIdentity #. generateFrameM .# fmap Identity


type GenerateFrameMaybe m df hf cols =
    ( EmptyFrame df
    , ExtendFrameMaybe m df hf '[] cols
    )


generateFrameMaybeM :: forall df cols hf m.
    ( GenerateFrameMaybe m df hf cols
    , CompatibleFields df cols
    )
    => Indexer (m (Maybe (hf Field cols)))
    -> m (df cols)
generateFrameMaybeM (Indexer n imfield) =
    extendFrameWithMaybeM (\_ new -> new)
        (imfield <$> getRowIndex)
        (emptyFrame n)


generateFrameMaybe :: forall df cols hf.
    ( GenerateFrameMaybe Identity df hf cols
    , CompatibleFields df cols
    )
    => Indexer (Maybe (hf Field cols))
    -> df cols
generateFrameMaybe =
    runIdentity #. generateFrameMaybeM .# fmap Identity
-}
