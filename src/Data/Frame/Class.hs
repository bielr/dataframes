{-# language MagicHash #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
{-# language QuantifiedConstraints #-}
module Data.Frame.Class where

import Prelude hiding ((.))
import GHC.TypeLits (KnownSymbol)

import Control.Category (Category(..))
import Control.Lens qualified as L
import Data.Coerce
import Data.Profunctor.Unsafe
import Data.Type.Coercion

import Data.Frame.Field
import Data.Frame.Kind
import Data.Frame.TypeIndex
import Data.Heterogeneous.Class.HCoerce
import Data.Heterogeneous.Class.HFoldable
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.Class.TupleView
import Data.Heterogeneous.Constraints
import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.HTuple
import Data.Indexer



type KnownField :: FrameK -> FieldK -> Constraint

class
    ( col ~ (FieldName col :> FieldType col)
    , KnownSymbol (FieldName col)
    , KnownDataType df (FieldType col)
    )
    => KnownField df col

instance
    ( col ~ (FieldName col :> FieldType col)
    , KnownSymbol (FieldName col)
    , KnownDataType df (FieldType col)
    )
    => KnownField df col


type IsFrame :: FrameK -> Constraint

class
    -- Env must be an Applicative functor
    ( forall cols. Applicative (Env df cols)
    -- Env df cols must have a representational argument
    , forall cols a b. Coercible a b => Coercible (Env df cols a) (Env df cols b)
    )
    => IsFrame df where

    type KnownDataType df :: Type -> Constraint

    frameLength :: df cols -> Int

    type Record df :: RecK

    data Column df :: FieldK -> Type

    colFields ::
        ( KnownField df col
        , KnownField df col'
        )
        => L.Iso (Column df col) (Column df col') (Indexer (Field col)) (Indexer (Field col'))

    data Env df :: FieldsK -> Type -> Type

    runEnv :: df cols -> Env df cols a -> Indexer a


class
    ( IsFrame df
    , HGetI (Record df) col cols i
    )
    => GetCol df col cols i where
    getCol :: IsFieldsProxy cols i proxy => proxy -> Env df cols (FieldType col)


col :: forall col cols i df proxy.
    ( IsFieldsProxy cols i proxy
    , GetCol df col cols i
    )
    => proxy
    -> Env df cols (FieldType col)
col = getCol



class IsFrame df => Columnar df hf cols | df -> hf where
    unsafeFromColsLength :: Int -> hf (Column df) cols -> df cols

    toCols :: df cols -> hf (Column df) cols


infixr 0 =.
infixr 0 =..


(=.) :: IsNameProxy s proxy => proxy -> a -> Field (s :> a)
_ =. a = Field a


(=..) ::
    ( IsNameProxy s proxy
    , Coercible (f a) (Column df (s :> a))
    )
    => proxy
    -> f a
    -> Column df (s :> a)
_ =.. fa = coerce fa


fromColsMaybe :: forall cols df hf.
    ( HFoldable hf cols
    , Columnar df hf cols
    , All (KnownField df) cols
    )
    => hf (Column df) cols
    -> Maybe (df cols)
fromColsMaybe cols =
    let lengths :: hf (Column df) cols -> [Int]
        lengths = hitoListWith $
            constrained @(KnownField df) @cols $
                length . L.view colFields
    in
        case lengths cols of
            []     -> Just (unsafeFromColsLength 0 cols)
            (l:ls)
              | all (==l) ls -> Just (unsafeFromColsLength l cols)
              | otherwise    -> Nothing


fromCols_ ::
    ( HFoldable hf cols
    , Columnar df hf cols
    , All (KnownField df) cols

    , TupleView hf cols
    , HCoerce HTuple cols
    , IsTupleOf map_column_cols t
    , Mapped (Column df) cols map_column_cols
    )
    => t
    -> Maybe (df cols)
fromCols_ = fromColsMaybe . fromHTuple .# coerceWith (hIdLCo . hconOutCo . htupleCo)


-- multicol :: forall cols' is cols df proxy.
--     ( IsFieldsProxy cols is proxy
--     , cols' ~ IndexAll cols is
--     , IsFrame df
--     )
--     => proxy
--     -> Env df cols (df cols')
-- multicol = undefined


-- record :: forall ss as cols.
--     ( cols ~ ZipWith (:>) ss as
--     , Coercible (TupleOf as) (HTuple Field cols)
--     )
--     => TupleOf as
--     -> HTuple Field cols
-- record = coerce
