{-# language MagicHash #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
{-# language QuantifiedConstraints #-}
module Data.Frame.Class where

import Prelude hiding ((.))

import Control.Category (Category(..))
import Data.Coerce
import Data.Profunctor.Unsafe

import Data.Frame.Field
import Data.Frame.Kind
import Data.Frame.Series.Class
import Data.Frame.TypeIndex
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.Constraints
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


class
    ( IsFrame df
    , (cols !! i) ~ col
    )
    => HasColumn df col cols i where

    findColumn :: IsFieldsProxy cols i proxy => proxy -> df cols -> Column df col

    findField :: IsFieldsProxy cols i proxy => proxy -> Env df cols (Field col)


    default findColumn ::
        ( IsFieldsProxy cols i proxy
        , Columnar df hf cols
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


class IsFrame df => Columnar df hf cols | df -> hf where
    toCols :: df cols -> hf (Column df) cols


class IsFrame df => Append df cols col where
    appendCol :: df cols -> Env df cols (Field col) -> df (cols ++ '[col])
    prependCol :: df cols -> Env df cols (Field col) -> df (col ': cols)


class IsFrame df => Transmute df cols hf cols' where
    transmute :: df cols -> Env df cols (hf Field cols') -> df cols'


fld :: forall col cols i df proxy.
    ( IsFieldsProxy cols i proxy
    , HasColumn df col cols i
    )
    => proxy
    -> Env df cols (Field col)
fld = findField

val :: forall col cols i df proxy.
    ( IsFieldsProxy cols i proxy
    , HasColumn df col cols i
    )
    => proxy
    -> Env df cols (FieldType col)
val = fmap getField #. fld


infixr 0 =.
infixr 0 =..


(=.) :: IsNameProxy s proxy => proxy -> a -> Field (s :> a)
_ =. a = Field a


(=..) ::
    IsNameProxy s proxy
    => proxy
    -> series (s :> a)
    -> series (s :> a)
_ =.. fa = fa


-- record :: forall ss as cols.
--     ( cols ~ ZipWith (:>) ss as
--     , Coercible (TupleOf as) (HTuple Field cols)
--     )
--     => TupleOf as
--     -> HTuple Field cols
-- record = coerce
