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
import Data.Coerce
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
import Data.Heterogeneous.Class.HCreate
import Data.Heterogeneous.Class.HMonoid
import Data.Heterogeneous.Class.HFoldable
import Data.Heterogeneous.Class.HTraversable
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.Class.Subseq
import Data.Heterogeneous.Class.TupleView
import Data.Heterogeneous.Constraints
import Data.Heterogeneous.HSmallArray (HSmallArray)
import Data.Heterogeneous.HTuple
import Data.Heterogeneous.TypeLevel


type Frame :: FrameK
data Frame cols = Frame
    { _nrow    :: !Int
    , _columns :: !(HSmallArray VectorSeries cols)
    }

makeLenses ''Frame


instance IsFrame Frame where
    frameLength (Frame n _) = n

    type instance Column Frame = VectorSeries

    -- type Env :: FieldsK -> Type -> Type -> Type
    -- type role Env nominal nominal nominal representational
    newtype Env Frame cols a = FrameEnv (Rowwise (Frame cols) a)
        deriving newtype (Functor, Applicative)

    withFrame f = FrameEnv (withCtx f)
    getRowIndex = FrameEnv rowid

    runEnv df@(Frame n _) (FrameEnv rww) = Indexer n $! runRowwise rww df


instance (CompatibleField VectorSeries col, HGetI HSmallArray col cols i) => HasColumn Frame col cols i


instance Columnar Frame HSmallArray cols where
    toCols (Frame _ cols) = cols


checkLengths :: HasCallStack => Int -> Int -> Int
checkLengths !n !m
  | n == m    = n
  | otherwise = error $
        "data frame length mismatch: " ++ show n ++ " /= " ++ show m
{-# inline checkLengths #-}


-- this ensures that the user does not modify the length of the frame
-- throws error if not preserved!
frameOfLength :: forall cols cols'.
    HasCallStack
    => Int
    -> Iso
        (HSmallArray VectorSeries cols) (HSmallArray VectorSeries cols')
        (Frame cols)                    (Frame cols')
frameOfLength n =
    iso (Frame n) deframe
  where
    deframe :: Frame cols' -> HSmallArray VectorSeries cols'
    deframe (Frame m cs) = checkLengths n m `seq` cs
{-# inline frameOfLength #-}


fromColsMaybe :: forall cols.
    ( KnownLength cols
    , CompatibleFields Frame cols
    )
    => HSmallArray VectorSeries cols
    -> Maybe (Frame cols)
fromColsMaybe cols =
    let lengths :: HSmallArray VectorSeries cols -> [Int]
        lengths = hitoListWith $
            constrained @(CompatibleField VectorSeries) @cols $
                view (from _VectorSeries . to VG.length)
    in
        case lengths cols of
            []     -> Just (Frame 0 cols)
            (l:ls)
              | all (==l) ls -> Just (Frame l cols)
              | otherwise    -> Nothing


fromCols_ :: forall cols series_cols t.
    ( KnownLength cols
    , CompatibleFields Frame cols

    , TupleView HSmallArray cols
    , HCoerce HTuple cols
    , IsTupleOf series_cols t
    , Mapped VectorSeries cols series_cols
    )
    => t
    -> Maybe (Frame cols)
fromCols_ = fromColsMaybe . fromHTuple .# coerceWith (hIdLCo . hconOutCo . htupleCo)



newCol ::
    CompatibleField VectorSeries col
    => Frame cols
    -> Env Frame cols (Field col)
    -> VectorSeries col
newCol df env = generateSeries (runEnv df (coerce env))


prependCol ::
    CompatibleField VectorSeries col
    => Env Frame cols (Field col)
    -> Frame cols
    -> Frame (col ': cols)
prependCol env df@(Frame n cols) =
    Frame n (newCol df env `hcons` cols)


appendCol ::
    CompatibleField VectorSeries col
    => Env Frame cols (Field col)
    -> Frame cols
    -> Frame (cols ++ '[col])
appendCol env df@(Frame n cols) =
    Frame n (cols `hsnoc` newCol df env)


restricting :: forall is cols1' cols2' cols1 cols2 proxy.
    ( IsFieldsProxy cols1 is proxy
    , HSubseqI HSmallArray cols1' cols2' cols1 cols2 is
    )
    => proxy
    -> Lens (Frame cols1) (Frame cols2) (Frame cols1') (Frame cols2')
restricting _ f df@(Frame n _) =
    (columns . hsubseqI @_ @cols1' @cols2' @cols1 @cols2 @is . frameOfLength n) f df



type FieldWriter :: Type -> FieldK -> Type
newtype FieldWriter s col = FieldWriter
    { writeField :: Int -> Field col -> ST.ST s ()
    }


generateCols :: forall cols' cols t.
    ( KnownLength cols'

    , HCoerce HTuple cols'
    , HTraversable HTuple cols'
    , TupleView HSmallArray cols'

    , IsTupleOf (TupleMembers t) t
    , Mapped Field cols' (TupleMembers t)

    , CompatibleFields Frame cols'
    )
    => Env Frame cols t
    -> Frame cols
    -> Frame cols'
generateCols (FrameEnv rww) df@(Frame n _) = ST.runST do
    let tupleGen :: Int -> t
        !tupleGen = runRowwise rww df

        fieldCo :: t :~>: HTuple Field cols'
        !fieldCo = hIdLCo . hconOutCo . htupleCo

        fieldsGen :: Int -> HTuple Field cols'
        !fieldsGen = gcoerceWith fieldCo (coerce tupleGen)

    mcols' <- initMVs

    let writers = toWriters mcols'

    forM_ [0..n-1] \i ->
        htraverse2_ (\w a -> writeField w i a)
            writers
            (fieldsGen i)

    cols' <- freezeCols mcols'

    return (Frame n cols')
  where
    initMVs :: ST.ST s (HSmallArray (MVectorSeries s) cols')
    initMVs =
        hcreateA $
            constrained @(CompatibleField VectorSeries) @cols' $
                MVectorSeries <$> VGM.unsafeNew n

    freezeCols :: HSmallArray (MVectorSeries s) cols' -> ST.ST s (HSmallArray VectorSeries cols')
    freezeCols =
        hitraverse $
            constrained @(CompatibleField VectorSeries) @cols' \(MVectorSeries mv) ->
                VectorSeries <$> VG.unsafeFreeze mv

    toWriters :: HSmallArray (MVectorSeries s) cols' -> HTuple (FieldWriter s) cols'
    toWriters =
        htupleWithC @_ @_ @(CompatibleField VectorSeries) \(MVectorSeries mv) ->
            FieldWriter (\i a -> VGM.unsafeWrite mv i (getField a))
