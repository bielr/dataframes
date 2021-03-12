{-# language MagicHash #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
{-# language QuantifiedConstraints #-}
module Data.Frame.Class where

import GHC.TypeLits (KnownSymbol)
import Data.Frame.Kind
import Data.Frame.TypeIndex
import Data.Heterogeneous.Class.Member


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


type IsFrame :: FrameK -> RecK -> Constraint

class
    (forall cols. Applicative (Env df cols))
    => IsFrame df rec | df -> rec where

    type KnownDataType df :: Type -> Constraint

    data Env df :: FieldsK -> Type -> Type

    col :: forall col cols i proxy.
        ( FieldSpecProxy col cols i proxy
        , KnownField df col
        , HGet rec col cols
        )
        => proxy
        -> Env df cols (FieldType col)


multicol :: forall cols' cols df rec is proxy.
    ( FieldSpecProxy cols' cols is proxy
    , IsFrame df rec
    )
    => proxy
    -> Env df cols (df cols')
multicol = undefined


-- record :: forall ss as cols.
--     ( cols ~ ZipWith (:>) ss as
--     , Coercible (TupleOf as) (HTuple Field cols)
--     )
--     => TupleOf as
--     -> HTuple Field cols
-- record = coerce
