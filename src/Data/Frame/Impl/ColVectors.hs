--{-# options_ghc -ddump-simpl -dsuppress-idinfo -dsuppress-unfoldings -dsuppress-coercions #-}
{-# language ApplicativeDo #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language RoleAnnotations #-}
{-# language TemplateHaskell #-}
{-# language UndecidableInstances #-}
module Data.Frame.Impl.ColVectors where

import Prelude hiding ((.))

import GHC.Stack

import Control.Category (Category(..))
import Control.Lens hiding ((:>))
import Control.Monad
import Control.Monad.ST qualified as ST
import Control.Rowwise
import Data.Profunctor.Unsafe
import Data.Type.Coercion
import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Mutable qualified as VGM

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

    runEval df@(Columns n _) (RowwiseEval rww) = Indexer n $! runRowwise rww df


evalColumn :: forall col cols df.
    ( IsFrame df
    , GenerateSeries (Column df)
    , CompatibleDataType (Column df) (FieldType col)
    )
    => df cols
    -> Eval df cols (FieldType col)
    -> Column df col
evalColumn df = generateSeries . runEval df


instance
    ( IsSeries series
    , CompatibleField series (cols !! i)
    , HGetI hf cols i
    )
    => HasColumnAt (Columns hf series) cols i


instance IsSeries series => ColumnarFrame (Columns hf series) where
    type ColumnarHRep (Columns hf series) = hf
    toCols (Columns _ cols) = cols


instance IsSeries series => ColumnarFrameEdit (Columns hf series) where
    editColsWith f (Columns n cols) = Columns n (f cols)


instance GenerateSeries series => InsertColumn (Columns hf series) where
    insertColumnWith insert ecol df@(Columns n cols) =
        Columns n (insert cols (evalColumn df (getField <$> ecol)))


-- instance (IsSeries series, HSingleton hf) => FromSingleColumn (Columns hf series) where
--     fromSingleCol series = Columns (seriesLength series) (hsingleton # series)


instance
    ( IsSeries series
    , IsSeries series'
    , hf ~ hf'
    , series ~ series'
    )
    => FrameMerge (Columns hf series) (Columns hf' series') where

    type MergedFrame (Columns hf series) (Columns hf' series') = Columns hf series

    unsafeMergeFramesWith weave (Columns n cols) (Columns m cols') =
        Columns (checkLengths n m) (weave cols cols')


instance
    ( HCreate hg cols'
    , HTraversable hg cols'
    , HConv hg hf cols'
    )
    => ExtendFrame (Columns hf VectorSeries) hg cols' where

    extendFrameWith weave ecols' df@(Columns n cols) =
        Columns n $ weave cols (hconv (generateVecCols (runEval df ecols')))


instance
    ( HCreate hg cols
    , HTraversable hg cols
    , HConv hg hf cols
    )
    => GenerateFrame (Columns hf VectorSeries) hg cols where

    generateFrame gen@(Indexer n _) =
        Columns n $ hconv (generateVecCols gen)


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



type FieldWriter :: Type -> FieldK -> Type
newtype FieldWriter s col = FieldWriter
    { writeField :: Int -> Field col -> ST.ST s ()
    }


generateVecCols :: forall cols hf.
    ( HCreate hf cols
    , HTraversable hf cols
    , All (CompatibleField VectorSeries) cols
    )
    => Indexer (hf Field cols)
    -> hf VectorSeries cols
generateVecCols (Indexer n fieldsGen) = ST.runST do
    mcols' <- initMVs

    let writers = toWriters mcols'

    forM_ [0..n-1] \i ->
        htraverse2_ (\w a -> writeField w i a)
            writers
            (fieldsGen i)

    freezeCols mcols'
  where
    initMVs :: ST.ST s (hf (MVectorSeries s) cols)
    initMVs =
        hcreateA $
            constrained @(CompatibleField VectorSeries) @cols $
                MVectorSeries <$> VGM.unsafeNew n

    freezeCols :: hf (MVectorSeries s) cols -> ST.ST s (hf VectorSeries cols)
    freezeCols =
        hitraverse $
            constrained @(CompatibleField VectorSeries) @cols \(MVectorSeries mv) ->
                VectorSeries <$> VG.unsafeFreeze mv

    toWriters :: hf (MVectorSeries s) cols -> hf (FieldWriter s) cols
    toWriters =
        hmapC @(CompatibleField VectorSeries) \(MVectorSeries mv) ->
            FieldWriter (\i a -> VGM.unsafeWrite mv i (getField a))
