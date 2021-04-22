--{-# options_ghc -ddump-simpl -dsuppress-idinfo -dsuppress-unfoldings -dsuppress-coercions #-}
{-# language ApplicativeDo #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MagicHash #-}
{-# language RoleAnnotations #-}
{-# language TemplateHaskell #-}
{-# language UndecidableInstances #-}
module Data.Frame.Columns where

import Prelude hiding ((.))

import GHC.Exts (SPEC(..), Int(..), Int#, (+#), (<#), isTrue#)
import GHC.Stack

import Control.Category (Category(..))
import Control.Lens hiding ((:>))
import Control.Monad
import Control.Monad.ST qualified as ST
import Control.Monad.Primitive (MonadPrim, PrimMonad)
import Control.Rowwise
import Data.Profunctor.Unsafe
import Data.Roles
import Data.Type.Coercion
import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Mutable qualified as VGM
import Data.Vector.Unboxed qualified as VU
import Data.Vector.Unboxed.Mutable qualified as VUM

import Data.Frame.Class
import Data.Frame.Series.Class
import Data.Frame.Field
import Data.Frame.Kind
import Data.Frame.Series.VectorSeries
import Data.Frame.TypeIndex
import Data.Indexer
import Data.Heterogeneous.Class.HCoerce
import Data.Heterogeneous.Class.HConv
import Data.Heterogeneous.Class.HCreate
import Data.Heterogeneous.Class.HFoldable
import Data.Heterogeneous.Class.HFunctor
import Data.Heterogeneous.Class.HMonoid
import Data.Heterogeneous.Class.HTraversable
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.Class.Subseq
import Data.Heterogeneous.Class.TupleView
import Data.Heterogeneous.Constraints
import Data.Heterogeneous.HTuple
import Data.Heterogeneous.TypeLevel



type Columns :: RecK -> SeriesK -> FrameK
data Columns hf series cols = Columns
    { _nrow    :: !Int
    , _columns :: !(hf series cols)
    }

makeLenses ''Columns


instance IsSeries series => IsFrame (Columns hf series) where
    frameLength (Columns n _) = n

    type instance Column (Columns hf series) = series

    -- type Eval :: FieldsK -> Type -> Type -> Type
    -- type role Eval nominal nominal nominal representational
    newtype Eval (Columns hf series) cols a =
        RowwiseEval (Rowwise (Columns hf series cols) a)
        deriving newtype (Functor, Applicative)

    withFrame f = RowwiseEval (withCtx f)
    getRowIndex = RowwiseEval rowid

    runEval df@(Columns n _) (RowwiseEval rww) = Indexer n (runRowwise rww df)


instance Representational (Eval (Columns hf series) cols) where
    rep Coercion = Coercion


instance
    ( IsSeries series
    , CompatibleDataType series (FieldType (cols !! i))
    , HGetI hf cols i
    )
    => HasColumnAt (Columns hf series) cols i


instance
    ( TraversableSeries series
    , CompatibleDataType series (FieldType col)
    , CompatibleDataType series (FieldType col')
    , col' ~ FieldName col :> FieldType col'
    , HSetI hf col col' cols cols' i
    )
    => HasColumnTraversal (Columns hf series) col col' cols cols' i where

    columnValues _ =
        columns . hmemberI @_ @col @col' @cols @cols' @i . seriesValues


instance IsSeries series => ColumnarFrame (Columns hf series) where
    type ColumnarHRep (Columns hf series) = hf
    toCols (Columns _ cols) = cols


instance IsSeries series => ColumnarFrameEdit (Columns hf series) where
    editColsWith f (Columns n cols) = Columns n (f cols)


instance (HMonoid hf, IsSeries series) => EmptyFrame (Columns hf series) where
    emptyFrame n = Columns n hempty


instance IsSeries series => FrameMerge (Columns hf series) where
    unsafeMergeFramesWith weave (Columns n cols) (Columns m cols') =
        Columns (checkLengths n m) (weave cols cols')


instance GenerateSeries m series => InsertColumn m (Columns hf series) where
    insertColumnWithM insert emcol df@(Columns n cols) = do
        col <- evalColumnM df (fmap getField <$> emcol)
        return (Columns n (insert cols col))
    {-# inline insertColumnWithM #-}


instance {-# overlaps #-}
    ( All (CompatibleField VectorSeries) cols'
    , HCreate hg cols'
    , HTraversable hg cols'
    , HConv hg hf cols'
    )
    => ExtendFrame Identity (Columns hf VectorSeries) hg cols' where

    extendFrameWithM weave (RowwiseEval emcols') df@(Columns n cols) =
        let !ix# = runRowwise# emcols' df

            Columns _ cols' = ST.runST $
                generateColumnsM# n \i -> return (runIdentity (ix# i))
        in
            Identity (Columns n (cols `weave` hconv cols'))
    {-# inline extendFrameWithM #-}


instance {-# overlappable #-}
    ( PrimMonad m
    , All (CompatibleField VectorSeries) cols'
    , HCreate hg cols'
    , HTraversable hg cols'
    , HConv hg hf cols'
    )
    => ExtendFrame m (Columns hf VectorSeries) hg cols' where

    extendFrameWithM weave (RowwiseEval emcols') df@(Columns n cols) = do
        Columns _ cols' <- generateColumnsM# n $! runRowwise# emcols' df

        return (Columns n (cols `weave` hconv cols'))
    {-# inline extendFrameWithM #-}


instance {-# overlaps #-}
    ( All (CompatibleField VectorSeries) cols
    , All (CompatibleField VectorSeries) cols'
    , HCreate hg cols'
    , HTraversable hg cols'
    , HConv hg hf cols'
    , HFunctor hf cols
    )
    => ExtendFrameMaybe Identity (Columns hf VectorSeries) hg cols cols' where

    extendFrameWithMaybeM weave (RowwiseEval emcols') df@(Columns n cols) =
        let !ix# = runRowwise# emcols' df

            (preserved, Columns _ cols') = ST.runST $
                generateColumnsMaybeM# n \i -> return (runIdentity (ix# i))

            reindexCols = hmapC @(CompatibleField VectorSeries) $
                over (from _VectorSeries) (`VG.backpermute` VG.convert preserved)
        in
            Identity (Columns n (reindexCols cols `weave` hconv cols'))
    {-# inline extendFrameWithMaybeM #-}


instance {-# overlappable #-}
    ( PrimMonad m
    , All (CompatibleField VectorSeries) cols
    , All (CompatibleField VectorSeries) cols'
    , HCreate hg cols'
    , HTraversable hg cols'
    , HConv hg hf cols'
    , HFunctor hf cols
    )
    => ExtendFrameMaybe m (Columns hf VectorSeries) hg cols cols' where

    extendFrameWithMaybeM weave (RowwiseEval emcols') df@(Columns n cols) = do
        (preserved, Columns _ cols') <- generateColumnsMaybeM# n $! runRowwise# emcols' df

        let reindexCols = hmapC @(CompatibleField VectorSeries) $
                over (from _VectorSeries) (`VG.backpermute` VG.convert preserved)

        return (Columns n (reindexCols cols `weave` hconv cols'))
    {-# inline extendFrameWithMaybeM #-}


-- instance {-# overlaps #-}
--     ( HCreate hg cols
--     , HTraversable hg cols
--     , HConv hg hf cols
--     )
--     => GenerateFrame Identity (Columns hf VectorSeries) hg cols where
--
--     generateFrameM (Indexer n gen) =
--         Identity $
--             over columns hconv $
--                 ST.runST $
--                     generateColumnsM# n \i -> return (runIdentity (gen (I# i)))
--     {-# inline generateFrameM #-}
--
--
--     generateFrameMaybeM (Indexer n gen) =
--         Identity $
--             over columns hconv $
--                 ST.runST $
--                     generateColumnsMaybeM# n \i -> return (runIdentity (gen (I# i)))
--     {-# inline generateFrameMaybeM #-}
--
--
-- instance {-# overlappable #-}
--     ( PrimMonad m
--     , HCreate hg cols
--     , HTraversable hg cols
--     , HConv hg hf cols
--     )
--     => GenerateFrame m (Columns hf VectorSeries) hg cols where
--
--     generateFrameM (Indexer n genM) =
--         over columns hconv <$>
--             generateColumnsM# n \i -> genM (I# i)
--     {-# inline generateFrameM #-}
--
--
--     generateFrameMaybeM (Indexer n genM) =
--         over columns hconv <$>
--             generateColumnsMaybeM# n \i -> genM (I# i)
--     {-# inline generateFrameMaybeM #-}


fromColsMaybe :: forall cols hf series.
    ( IsSeries series
    , HFoldable hf cols
    , All (CompatibleField series) cols
    )
    => hf series cols
    -> Maybe (Columns hf series cols)
fromColsMaybe cols =
    let lengths :: hf series cols -> [Int]
        lengths = hitoListWith $
            constrained @(CompatibleField series) @cols $
                length . indexSeries
    in
        case lengths cols of
            []     -> Just (Columns 0 cols)
            (l:ls)
              | all (==l) ls -> Just (Columns l cols)
              | otherwise    -> Nothing


fromCols_ :: forall cols hf series t.
    ( IsSeries series
    , HFoldable hf cols

    , KnownLength cols
    , All (CompatibleField series) cols

    , TupleView hf cols
    , HCoerce HTuple cols
    , IsTupleOfF series cols t
    )
    => t
    -> Maybe (Columns hf series cols)
fromCols_ = fromColsMaybe . fromHTuple .# coerceWith (hIdLCo . hconOutCo . htupleCo)


-- unsafe! TODO: do better with a wrapper frame type
restricting :: forall is cols1' cols2' cols1 cols2 hf series proxy.
    ( IsFieldsProxy cols1 is proxy
    , HSubseqI hf cols1' cols2' cols1 cols2 is
    )
    => proxy
    -> Lens
        (Columns hf series cols1)  (Columns hf series cols2)
        (Columns hf series cols1') (Columns hf series cols2')
restricting _ f df@(Columns n _) =
    (columns . hsubseqI @_ @cols1' @cols2' @cols1 @cols2 @is . frameOfLength n) f df


------------ IMPLEMENTATION HELPERS -------------


checkLengths :: HasCallStack => Int -> Int -> Int
checkLengths !n !m
  | n == m    = n
  | otherwise = error $
        "data frame length mismatch: " ++ show n ++ " /= " ++ show m
{-# inline checkLengths #-}


-- this ensures that the user does not modify the length of the frame
-- throws error if not preserved!
frameOfLength ::
    HasCallStack
    => Int
    -> Iso
        (hf series cols)             (hf' series' cols')
        (Columns hf series cols)     (Columns hf' series' cols')
frameOfLength n =
    iso (Columns n) deframe
  where
    -- deframe :: Frame cols' -> HSmallArray VectorSeries cols'
    deframe (Columns m cs) = checkLengths n m `seq` cs
{-# inline frameOfLength #-}



type FieldWriter :: (Type -> Type) -> FieldK -> Type
newtype FieldWriter m col = FieldWriter
    { writeField :: Int# -> Field col -> m ()
    }


generateColumnsM# :: forall cols hf m s.
    ( MonadPrim s m
    , HCreate hf cols
    , HTraversable hf cols
    , All (CompatibleField VectorSeries) cols
    )
    => Int
    -> (Int# -> m (hf Field cols))
    -> m (Columns hf VectorSeries cols)
generateColumnsM# !n !fieldsGen = do
    mcols' <- initMVs

    let !writers = toWriters SPEC mcols'

    forM_ [0..n-1] \(I# i) -> do
        fields <- fieldsGen i

        htraverse2_ (\w a -> writeField w i a)
            writers
            fields

    cols' <- freezeCols mcols'

    return (Columns n cols')
  where
    initMVs :: m (hf (MVectorSeries s) cols)
    initMVs =
        hcreateA $
            constrained @(CompatibleField VectorSeries) @cols $
                MVectorSeries <$> VGM.unsafeNew n

    toWriters :: SPEC -> hf (MVectorSeries s) cols -> hf (FieldWriter m) cols
    toWriters !_SPEC =
        hmapC @(CompatibleField VectorSeries) \(MVectorSeries mv) ->
            FieldWriter (\i a -> VGM.unsafeWrite mv (I# i) (getField a))

    freezeCols :: hf (MVectorSeries s) cols -> m (hf VectorSeries cols)
    freezeCols =
        hitraverse $
            constrained @(CompatibleField VectorSeries) @cols \(MVectorSeries mv) ->
                VectorSeries <$> VG.unsafeFreeze mv
{-# inline generateColumnsM# #-}


generateColumnsMaybeM# :: forall cols hf m s.
    ( MonadPrim s m
    , HCreate hf cols
    , HTraversable hf cols
    , All (CompatibleField VectorSeries) cols
    )
    => Int
    -> (Int# -> m (Maybe (hf Field cols)))
    -> m (VU.Vector Int, Columns hf VectorSeries cols)
generateColumnsMaybeM# n@(I# n#) !fieldsGenM = do
    mchangelog <- VUM.unsafeNew n
    mcols' <- initMVs

    let !writers = toWriters SPEC mcols'

        go (i :: Int#) (len :: Int#)
            | isTrue# (i <# n#) =
                  fieldsGenM i >>= \case
                      Nothing ->
                          go (i +# 1#) len
                      Just row -> do
                          VUM.unsafeWrite mchangelog (I# len) (I# i)
                          htraverse2_ (\w a -> writeField w len a) writers row
                          go (i +# 1#) (len +# 1#)
            | otherwise = return (I# len)

    n' <- go 0# 0#

    changelog <-
        if n' < n then
            VG.freeze (VGM.take n' mchangelog)
        else
            VG.unsafeFreeze mchangelog

    cols' <- freezeCols n' mcols'

    return (changelog, Columns n' cols')
  where
    initMVs :: m (hf (MVectorSeries s) cols)
    initMVs =
        hcreateA $
            constrained @(CompatibleField VectorSeries) @cols $
                MVectorSeries <$> VGM.unsafeNew n

    toWriters :: SPEC -> hf (MVectorSeries s) cols -> hf (FieldWriter m) cols
    toWriters !_SPEC =
        hmapC @(CompatibleField VectorSeries) \(MVectorSeries mv) ->
            FieldWriter (\i a -> VGM.unsafeWrite mv (I# i) (getField a))


    freezeCols :: Int -> hf (MVectorSeries s) cols -> m (hf VectorSeries cols)
    freezeCols n'
        | n' < n =
            hitraverse $
                constrained @(CompatibleField VectorSeries) @cols \(MVectorSeries mv) -> do
                    VectorSeries <$> VG.freeze (VGM.take n' mv)
        | otherwise =
            hitraverse $
                constrained @(CompatibleField VectorSeries) @cols \(MVectorSeries mv) -> do
                    VectorSeries <$> VG.unsafeFreeze mv
{-# inline generateColumnsMaybeM# #-}
