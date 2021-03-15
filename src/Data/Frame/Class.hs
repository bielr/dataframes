{-# language MagicHash #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
{-# language QuantifiedConstraints #-}
module Data.Frame.Class where

import GHC.TypeLits (KnownSymbol)
import Data.Frame.Kind
import Data.Frame.TypeIndex
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.TypeLevel
import Type.Errors


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

    col :: forall i col cols proxy.
        IsFieldsProxy cols i proxy
        =>
        ( KnownField df col
        , HGetI rec col cols i
        )
        => proxy
        -> Env df cols (FieldType col)


type PrettyPrintField :: FieldK -> ErrorMessage
type family PrettyPrintField col where
    PrettyPrintField (s :> a) = 'Text ", " ':<>: 'ShowType (s :> a)


type PrettyPrintFields :: FieldsK -> ErrorMessage
type family PrettyPrintFields cols where
    PrettyPrintFields '[]           = 'Text ""
    PrettyPrintFields (col ': cols) =
        PrettyPrintField col
        ':$$: 'Text ""
            ':<>: PrettyPrintFields cols


type PrettyPrintFrameType :: FrameK -> FieldsK -> ErrorMessage
type PrettyPrintFrameType df cols =
    'Text "At this point, the type of the data frame is "
    ':$$: 'ShowType df
        ':<>: 'Text " '["
    ':$$: 'Text "    "
        ':<>: PrettyPrintFields cols
        ':<>: 'Text "]"


printFrameType :: forall (df :: FrameK) cols.
    DelayError (PrettyPrintFrameType df cols)
    => df cols
    -> df cols
printFrameType df = df


multicol :: forall (is :: [Peano]) cols' cols df rec proxy.
    ( IsFieldsProxy cols is proxy
    , cols' ~ IndexAll cols is
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
