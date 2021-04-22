{-# language MagicHash #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language UndecidableInstances #-}
module Data.Frame.Zoomed where

import GHC.Exts (Proxy#, proxy#)

import Control.Category ((<<<))
import Control.Lens

import Data.Roles
import Data.Type.Coercion

import Data.Frame.Class
import Data.Frame.TypeIndex
import Data.Heterogeneous.Class.Subseq
import Data.Heterogeneous.TypeLevel.Subseq


data ZoomedFrame x df cols = ZoomedFrame !x !(df cols)

instance IsFrame df => IsFrame (ZoomedFrame x df) where
    type Column (ZoomedFrame x df) = Column df

    frameLength (ZoomedFrame _ df) = frameLength df

    newtype Eval (ZoomedFrame x df) cols a = ZoomedEval (x -> Eval df cols a)

    withFrame prj = ZoomedEval \ !x -> withFrame (\df -> prj (ZoomedFrame x df))
    getRowIndex = ZoomedEval \ !_ -> getRowIndex

    runEval (ZoomedFrame x df) (ZoomedEval xea) = runEval df (xea x)


withHidden :: IsFrame df => (x -> a) -> Eval (ZoomedFrame x df) cols a
withHidden prj = ZoomedEval \ !x ->
    let !a = prj x
    in  pure a


zoomedEvalCo :: Coercion (x -> Eval df cols a) (Eval (ZoomedFrame x df) cols a)
zoomedEvalCo = Coercion


instance IsFrame df => Representational (Eval (ZoomedFrame x df) cols) where
    rep co = zoomedEvalCo <<< rep (rep co) <<< sym zoomedEvalCo


instance Functor (Eval df cols) => Functor (Eval (ZoomedFrame x df) cols) where
    fmap f (ZoomedEval xea) = ZoomedEval $! fmap f . xea


instance Applicative (Eval df cols) => Applicative (Eval (ZoomedFrame x df) cols) where
    pure a =
        ZoomedEval \ !_ -> pure a

    ZoomedEval xef <*> ZoomedEval xea =
        ZoomedEval \ !x -> xef x <*> xea x


instance HasColumnAt df cols i => HasColumnAt (ZoomedFrame x df) cols i where
    findColumn proxy (ZoomedFrame _ df) = findColumn proxy df


instance HasColumnTraversal df col col' cols cols' i
    => HasColumnTraversal (ZoomedFrame x df) col col' cols cols' i where

    columnValues proxy f (ZoomedFrame x df) =
        ZoomedFrame x <$> columnValues proxy f df


instance ColumnarFrame df => ColumnarFrame (ZoomedFrame x df) where
    type ColumnarHRep (ZoomedFrame x df) = ColumnarHRep df

    toCols (ZoomedFrame _ df) = toCols df


instance ColumnarFrameEdit df => ColumnarFrameEdit (ZoomedFrame x df) where
    editColsWith edit (ZoomedFrame x df) = ZoomedFrame x (editColsWith edit df)

    splitFrameWith split (ZoomedFrame x df) =
        case splitFrameWith split df of
            (df', df'') -> (ZoomedFrame x df', ZoomedFrame x df'')


instance InsertColumn m df => InsertColumn m (ZoomedFrame x df) where
    insertColumnWithM insert (ZoomedEval xecol) (ZoomedFrame x df) =
        ZoomedFrame x <$> insertColumnWithM insert (xecol x) df


instance ExtendFrame m df hf cols' => ExtendFrame m (ZoomedFrame x df) hf cols' where
    extendFrameWithM weave (ZoomedEval xecol) (ZoomedFrame x df) =
        ZoomedFrame x <$> extendFrameWithM weave (xecol x) df


zoomIn :: forall cols df is xcols cols'.
    ( ColumnarFrameEdit df
    , HQuotientI (ColumnarHRep df) cols' cols xcols is
    )
    => Proxy# is
    -> df cols
    -> ZoomedFrame (df xcols) df cols'
zoomIn _ df =
    case splitFrameWith (view (hsubseqSplitI @_ @_ @_ @_ @is)) df of
        (df', xdf) -> ZoomedFrame xdf df'


zoomOut :: forall cols df is xcols cols'.
    ( FrameMerge df
    , HQuotientI (ColumnarHRep df) cols' cols xcols is
    )
    => Proxy# is
    -> ZoomedFrame (df xcols) df cols'
    -> df cols
zoomOut _ (ZoomedFrame xdf df) =
    unsafeMergeFramesWith
        (\xcols cols' -> hsubseqSplitI @_ @_ @_ @_ @is # (cols', xcols))
        xdf
        df


forget :: Zoomed x df cols -> df cols
forget (Zoomed _ df) = df


zooming' :: forall cols0' cols1' xcols cols0 cols1 is df proxy.
    ( IsFieldsProxy cols0 is proxy

    , FrameMerge df
    , HSubseqI (ColumnarHRep df) cols0' cols1' cols0 cols1 is
    , HQuotientI (ColumnarHRep df) cols0' cols0 xcols is
    , HQuotientI (ColumnarHRep df) cols1' cols1 xcols (IndexesOfSubseq cols1' cols1)
    )
    => proxy
    -> Iso (df cols0)                         (df cols1)
           (ZoomedFrame (df xcols) df cols0') (ZoomedFrame (df xcols) df cols1')
zooming' _ =
    iso (zoomIn (proxy# @is))
        (zoomOut (proxy# @(IndexesOfSubseq cols1' cols1)))
