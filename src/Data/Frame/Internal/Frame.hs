{-# language GADTs #-}
{-# language PatternSynonyms #-}
{-# language QuantifiedConstraints #-}
{-# language StrictData #-}
{-# language UndecidableInstances #-}
{-# language ViewPatterns #-}
module Data.Frame.Internal.Frame where

import GHC.Stack (HasCallStack)

import Control.Applicative (liftA2)
import Control.Lens.Type
import Control.Lens qualified as L
import Control.Monad.ST (runST)

import Data.Foldable
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semigroup
import Data.Type.Equality ((:~:)(..))
import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Mutable qualified as VGM
import Data.Vinyl.TypeLevel (NatToInt(..), RLength, type (++))

import Data.Frame.Field
import Data.Frame.Internal.Column
import Data.Frame.Internal.Repr
import Data.Frame.Kind
import Data.Frame.Row
import Data.Indexer
import Data.Vinyl.Extra


data Frame (rep :: Repr) (by :: Major) (rec :: RecK) cols where
    ColGens :: Int -> rec (Col 'Idx) cols        -> Frame 'Idx 'Cols rec cols
    ColVecs :: Int -> rec (Col 'Vec) cols        -> Frame 'Vec 'Cols rec cols
    RowsGen ::        Indexer   (rec Field cols) -> Frame 'Idx 'Rows rec cols
    RowsVec ::        RowVector (rec Field cols) -> Frame 'Vec 'Rows rec cols


instance Semigroup (Frame 'Idx 'Rows rec cols) where
    RowsGen rs1 <> RowsGen rs2 = RowsGen (rs1 <> rs2)
    sconcat = RowsGen . sconcat . fmap (L.view frameRows)


instance Semigroup (Frame 'Vec 'Rows rec cols) where
    RowsVec rs1 <> RowsVec rs2 = RowsVec (rs1 <> rs2)
    sconcat = RowsVec . sconcat . fmap (L.view frameRows)


instance RDistributive rec cols => Semigroup (Frame 'Idx 'Cols rec cols) where
    ColGens n cs1 <> ColGens m cs2 =
        ColGens
            (n + m)
            (rzipWith appendCols cs1 cs2)

    sconcat frames =
        ColGens
            (L.sumOf (L.folded . colsLength) frames)
            (rcotraverse
                (concatCols . toList)
                (fmap (L.view colsRec) frames))


instance (RDistributive rec cols, ColTypes cols) => Semigroup (Frame 'Vec 'Cols rec cols) where
    ColVecs n cs1 <> ColVecs m cs2 =
        ColVecs
            (n + m)
            (rizipWith (constrained @ColType @cols appendCols) cs1 cs2)

    sconcat frames =
        ColVecs
            (L.sumOf (L.folded . colsLength) frames)
            (ricotraverse
                (constrained @ColType @cols (concatCols . toList))
                (fmap (L.view colsRec) frames))


instance Monoid (Frame 'Idx 'Rows rec cols) where
    mempty = RowsGen mempty

    mconcat []     = mempty
    mconcat (x:xs) = sconcat (x :| xs)


instance Monoid (Frame 'Vec 'Rows rec cols) where
    mempty = RowsVec mempty

    mconcat []     = mempty
    mconcat (x:xs) = sconcat (x :| xs)


instance (RDistributive rec cols, RNew rec cols) => Monoid (Frame 'Idx 'Cols rec cols) where
    mempty = ColGens 0 (rnew emptyCol)

    mconcat []     = mempty
    mconcat (x:xs) = sconcat (x :| xs)


instance (RDistributive rec cols, RNew rec cols, ColTypes cols) => Monoid (Frame 'Vec 'Cols rec cols) where
    mempty = ColVecs 0 (rinew $ constrained @ColType @cols emptyCol)

    mconcat []     = mempty
    mconcat (x:xs) = sconcat (x :| xs)


frameCaseMajor :: Frame rep by rec cols -> Either (by :~: 'Rows) (by :~: 'Cols)
frameCaseMajor (ColGens _ _) = Right Refl
frameCaseMajor (ColVecs _ _) = Right Refl
frameCaseMajor (RowsGen _)   = Left Refl
frameCaseMajor (RowsVec _)   = Left Refl
{-# inline frameCaseMajor #-}


pattern ByCols :: () => (by ~ 'Cols) => Frame rep by rec cols
pattern ByCols <- (frameCaseMajor -> Right Refl)


pattern ByRows :: () => (by ~ 'Rows) => Frame rep by rec cols
pattern ByRows <- (frameCaseMajor -> Left Refl)


{-# complete ByCols, ByRows #-}
{-# complete ByCols, RowsGen, RowsVec #-}
{-# complete ByRows, ColVecs, ColGens #-}


checkLengths :: HasCallStack => Int -> Int -> Int
checkLengths !n !m
  | n == m    = n
  | otherwise = error $
        "Frame.checkLength: data frame length mismatch: " ++ show n ++ " /= " ++ show m
{-# inline checkLengths #-}


frameRows ::
    Lens
      (Frame rep 'Rows rec cols)      (Frame rep 'Rows rec' cols')
      (RowsRepF rep (rec Field cols)) (RowsRepF rep (rec' Field cols'))
frameRows f df =
    case df of
      RowsVec rows -> RowsVec <$> f rows
      RowsGen rows -> RowsGen <$> f rows
{-# inline frameRows #-}


-- internal, should only be exported as a Getter
colsRec ::
    Lens
      (Frame rep 'Cols rec cols) (Frame rep 'Cols rec' cols')
      (rec (Col rep) cols)       (rec' (Col rep) cols')
colsRec f = \case
    ColVecs n cs -> ColVecs n <$> f cs
    ColGens n cs -> ColGens n <$> f cs
{-# inline colsRec #-}


-- internal, should not be exposed to ensure data frame consistency
colsLength :: Lens' (Frame rep 'Cols rec cols) Int
colsLength f = \case
    ColVecs n cs -> fmap (\n' -> ColVecs n' cs) (f n)
    ColGens n cs -> fmap (\n' -> ColGens n' cs) (f n)
{-# inline colsLength #-}


-- this ensures that the user does not modify the length of the frame
-- throws error if not preserved!
asFrameOfLength :: forall rep rep' rec rec' cols cols'.
    (HasCallStack, KnownRepr rep)
    => Int
    -> Iso
        (rec (Col rep) cols)       (rec' (Col rep') cols')
        (Frame rep 'Cols rec cols) (Frame rep' 'Cols rec' cols')
asFrameOfLength n =
    case sRepr @rep of
      SVec -> L.iso (ColVecs n) deframe
      SIdx -> L.iso (ColGens n) deframe
  where
    deframe :: Frame rep' 'Cols rec' cols' -> rec' (Col rep') cols'
    deframe (ColVecs m cs) = checkLengths n m `seq` cs
    deframe (ColGens m cs) = checkLengths n m `seq` cs
{-# inline asFrameOfLength #-}


ncols :: forall cols rep by rec. NatToInt (RLength cols) => Frame rep by rec cols -> Int
ncols _ = natToInt @(RLength cols)
{-# inline ncols #-}


nrows :: Frame rep by rec cols -> Int
nrows = \case
    RowsVec v   -> length v
    RowsGen g   -> length g
    ColVecs n _ -> n
    ColGens n _ -> n
{-# inline nrows #-}


rowwise :: forall rep by rec cols.
    When (by == 'Cols)
      ( When (rep == 'Vec) (ColTypes cols)
      , RFunctor rec
      )
    => Frame rep by rec cols
    -> Frame rep 'Rows rec cols
rowwise df =
    case df of
      ByRows       -> df
      ColVecs n cs -> RowsVec $ VG.generate n (\i -> rmapC @ColType (L.^?! L.ix i) cs)
      ColGens n cs -> RowsGen $ Indexer     n (\i -> rmap           (L.^?! L.ix i) cs)


colwise :: forall rep rep' by rec cols.
    ( When (by == 'Cols) (rep' ~ rep)
    , When (by == 'Rows)
        ( rep' ~ 'Vec
        , ColTypes cols
        , RNew rec cols
        , RTraversable rec
        )
    )
    => Frame rep  by    rec cols
    -> Frame rep' 'Cols rec cols
colwise df@ByCols = df
colwise df@ByRows = runST do
    let RowsGen rows = indexFrame df
        n = length rows

    mcols <- rinewA $ constrained @ColType @cols $ unsafeNewMCol n

    L.iforM_ rows \j row ->
        rtraverse2_ (\(ColMVec mv) fa -> VGM.unsafeWrite mv j fa) mcols row

    cols <- rtraverse unsafeFreezeMCol mcols

    return (ColVecs n cols)


rmapCols :: forall rep rep' rec cols.
    ( When (rep == 'Vec || rep' == 'Vec) (ColTypes cols)
    , RFunctor rec
    , KnownRepr rep => KnownRepr rep'
    )
    => (forall col.
          (When (rep == 'Vec || rep' == 'Vec) (ColType col))
          => Col rep col
          -> Col rep' col)
    -> Frame rep  'Cols rec cols
    -> Frame rep' 'Cols rec cols
rmapCols h df =
    case df of
      ColVecs n cs ->
          case sRepr @rep' of
            SVec -> ColVecs n (rmapC @ColType h cs)
            SIdx -> ColGens n (rmapC @ColType h cs)
      ColGens n cs ->
          case sRepr @rep' of
            SVec -> ColVecs n (rmapC @ColType h cs)
            SIdx -> ColGens n (rmap h cs)


indexFrame ::
    When (by == 'Cols && rep == 'Vec) (ColTypes cols, RFunctor rec)
    => Frame rep  by rec cols
    -> Frame 'Idx by rec cols
indexFrame df =
    case df of
      RowsVec rows -> RowsGen (indexVector rows)
      RowsGen _    -> df
      ColVecs _ _  -> rmapCols indexCol df
      ColGens _ _  -> df


forceFrame ::
    When (by == 'Cols) (ColTypes cols, RFunctor rec)
    => Frame rep  by rec cols
    -> Frame 'Vec by rec cols
forceFrame df =
    case df of
      RowsVec rows -> RowsVec (VG.force rows)
      RowsGen rows -> RowsVec (copyIndexer rows)
      ByCols       -> rmapCols forceCol df


cbind ::
    RMonoid rec
    => Frame rep by rec cols
    -> Frame rep by rec cols'
    -> Frame rep by rec (cols ++ cols')
cbind df1 df2 =
    case (df1, df2) of
      (RowsGen rows1, RowsGen rows2) -> n `seq` RowsGen (liftA2     rappend rows1 rows2)
      (RowsVec rows1, RowsVec rows2) -> n `seq` RowsVec (VG.zipWith rappend rows1 rows2)
      (ColGens _ cs1, ColGens _ cs2) -> ColGens n (rappend cs1 cs2)
      (ColVecs _ cs1, ColVecs _ cs2) -> ColVecs n (rappend cs1 cs2)
  where
    n = checkLengths (nrows df1) (nrows df2)
