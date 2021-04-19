module Data.Frame.Sugar
    ( module Exports
    , C.IsFrame
    , C.HasColumn
    , C.ColumnarFrame
    , C.FromSingleColumn
    , C.ConcatCols
    , C.AppendCol
    , C.GenerateFrame
    , C.CompatibleFields
    , C.CompatibleDataTypes

    , C.Columns
    , HList
    , HSmallArray
    , HTuple(..)
    , VectorSeries

    , (=.)
    , (=..)
    , fld
    , val

    , Eval
    , C.frameLength
    , C.withFrame
    , C.getRowIndex

    , Frame
    , frameFromCols
    , C.generateFrame

    , C.appendCol
    , C.prependCol
    , transmute
    , transmute'
    , transmute2

    ) where

import GHC.Stack (HasCallStack)

import Data.Maybe (fromMaybe)
import Data.Profunctor.Unsafe
import Data.Type.Coercion

import Data.Frame.Class (Eval)
import Data.Frame.Class qualified as C
import Data.Frame.Field as Exports
import Data.Frame.Kind as Exports
import Data.Frame.Impl.ColVectors qualified as C
import Data.Frame.Series.Class as Exports
import Data.Frame.Series.VectorSeries (VectorSeries)
import Data.Frame.TypeIndex

import Data.Heterogeneous.Class.HCoerce
import Data.Heterogeneous.Class.TupleView
import Data.Heterogeneous.Constraints
import Data.Heterogeneous.HList
import Data.Heterogeneous.HSmallArray
import Data.Heterogeneous.HTuple
import Data.Heterogeneous.TypeLevel

import Data.Indexer as Exports


type Frame = C.Columns HSmallArray VectorSeries


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


fld :: forall col cols i df proxy.
    ( IsFieldsProxy cols i proxy
    , C.HasColumnAt df cols i
    , CompatibleField (C.Column df) col
    , col ~ cols !! i
    )
    => proxy
    -> Eval df cols (Field col)
fld = C.findField


val :: forall col cols i df proxy.
    ( IsFieldsProxy cols i proxy
    , C.HasColumnAt df cols i
    , CompatibleField (C.Column df) col
    , col ~ cols !! i
    )
    => proxy
    -> Eval df cols (FieldType col)
val = fmap getField #. fld


frameFromColsMaybe :: forall cols t.
    ( KnownLength cols

    , All (CompatibleField VectorSeries) cols

    , TupleView HSmallArray cols
    , HCoerce HTuple cols
    , IsTupleOfF VectorSeries cols t
    )
    => t
    -> Maybe (Frame cols)
frameFromColsMaybe = C.fromColsMaybe . fromHTuple .  coerceWith htupleCoF


frameFromCols :: forall cols t.
    ( HasCallStack
    , KnownLength cols

    , All (CompatibleField VectorSeries) cols

    , TupleView HSmallArray cols
    , HCoerce HTuple cols
    , IsTupleOfF VectorSeries cols t
    )
    => t
    -> Frame cols
frameFromCols =
    fromMaybe (error "frameFromCols: column length mismatch") . frameFromColsMaybe


transmute :: forall cols cols' t df df'.
    ( C.IsFrame df'
    , HCoerce HTuple cols'
    , IsTupleOfF Field cols' t
    , C.GenerateFrame df HTuple cols'
    , C.CompatibleFields df cols'
    )
    => Eval df' cols t
    -> df' cols
    -> df cols'
transmute et df =
    C.generateFrame (C.runEval df (C.coerceHTupleEval et))


transmute' :: forall cols cols' t df.
    ( HCoerce HTuple cols'
    , IsTupleOfF Field cols' t
    , C.GenerateFrame df HTuple cols'
    , C.CompatibleFields df cols'
    )
    => Eval df cols t
    -> df cols
    -> df cols'
transmute' = transmute


transmute2 :: forall cols cols' df.
    ( C.GenerateFrame df HList cols'
    , C.CompatibleFields df cols'
    )
    => Eval df cols (HList Field cols')
    -> df cols
    -> df cols'
transmute2 ecols' df = C.generateFrame (C.runEval df ecols')
