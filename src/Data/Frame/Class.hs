{-# language AllowAmbiguousTypes #-}
{-# language MagicHash #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
{-# language QuantifiedConstraints #-}
module Data.Frame.Class where

import GHC.Exts (Proxy#, proxy#)
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
    (forall cols tok. Applicative (Env df cols tok))
    => IsFrame df rec | df -> rec where

    type KnownDataType df :: Type -> Constraint

    data Env df :: FieldsK -> Type -> Type -> Type

    getCol :: forall col cols tok.
        ( HGet rec col cols
        , KnownField df col
        )
        => Proxy# col
        -> Env df cols tok (FieldType col)


col :: forall i col cols df rec tok.
    ( FieldSpec cols i col
    , IsFrame df rec
    , HGet rec col cols
    , KnownField df col
    )
    => Env df cols tok (FieldType col)
col = getCol (proxy# @col)
