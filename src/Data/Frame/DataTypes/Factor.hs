{-# language StrictData #-}
module Data.Frame.DataTypes.Factor where

import Control.Applicative
import Control.Monad.ST qualified as ST

import Data.Foldable.WithIndex
import Data.Indexer
import Data.Hashable (Hashable)
import Data.HashMap.Internal qualified as HM (unsafeInsert)
import Data.HashMap.Strict qualified as HM
import Data.Vector qualified as VB
import Data.Vector.Mutable qualified as VBM
import Data.Vector.Unboxed qualified as VU
import Data.Vector.Unboxed.Mutable qualified as VUM

import Data.Heterogeneous.HList
import Data.Heterogeneous.Functors




data Uniques a = Uniques
    { uniquesIdsMap   :: HM.HashMap a Int
    , uniquesIdVector :: VU.Vector Int
    }


uniquesNumDistinct :: Uniques a -> Int
uniquesNumDistinct = HM.size . uniquesIdsMap


data UniqState a = UniqState {-# unpack #-} Int (HM.HashMap a Int)


uniquesHashable :: (Eq a , Hashable a) => Indexer a -> Uniques a
uniquesHashable as = ST.runST do
    midVec <- VUM.unsafeNew (length as)

    let update !i (UniqState k ids) !a =
            case HM.lookup a ids of
                Nothing -> do
                    VUM.unsafeWrite midVec i k
                    return (UniqState (k+1) (HM.unsafeInsert a k ids))
                Just k' -> do
                    VUM.unsafeWrite midVec i k'
                    return (UniqState k ids)

    UniqState _ ids <- ifoldlM update (UniqState 0 HM.empty) as

    idVec <- VU.unsafeFreeze midVec

    return (Uniques ids idVec)


data FactorLevels a = FactorLevels
    { levelsLabels :: VB.Vector a
    , levelsIds    :: HM.HashMap a Int
    }


levelsSize :: FactorLevels a -> Int
levelsSize = VB.length . levelsLabels


data Factor a = Factor
    { factorLevels   :: FactorLevels a
    , factorIdVector :: VU.Vector Int
    }


factorLength :: Factor a -> Int
factorLength = VU.length . factorIdVector


indexFactor :: Factor a -> Indexer a
indexFactor f =
    indexVector (levelsLabels (factorLevels f))
        `backpermuteIndexer`
            indexVector (factorIdVector f)


collectLabels :: Uniques a -> Factor a
collectLabels (Uniques ids idVec) =
    Factor
        { factorLevels =
            FactorLevels
                { levelsLabels = VB.create do
                    mlabels <- VBM.unsafeNew (HM.size ids)
                    iforM_ ids (\a i -> VBM.unsafeWrite mlabels i a)
                    return mlabels
                , levelsIds = ids
                }
        , factorIdVector = idVec
        }


factorizeHashable :: (Eq a, Hashable a) => Indexer a -> Factor a
factorizeHashable = collectLabels . uniquesHashable


countLevelFreqs :: Factor a -> VU.Vector Int
countLevelFreqs (Factor lvs idVec) = VU.create do
    counts <- VUM.replicate (levelsSize lvs) 0
    VU.forM_ idVec (VUM.unsafeModify counts succ)
    return counts


factorGroupSortPermutation :: Factor a -> VU.Vector Int
factorGroupSortPermutation f@(Factor lvs idVec) = ST.runST do
    let !counts = countLevelFreqs f

    permutation <- VUM.unsafeNew (factorLength f)

    let !offsets = VU.prescanl' (+) 0 counts

    mlengths <- VUM.replicate (levelsSize lvs) 0

    VU.iforM_ idVec \i lvId -> do
        let offset = offsets `VU.unsafeIndex` lvId
        len <- VUM.unsafeRead mlengths lvId
        VUM.unsafeWrite permutation (offset+len) i
        VUM.unsafeWrite mlengths lvId (len+1)

    VU.unsafeFreeze permutation


data MultiFactor f as where
    SingleFactor    ::               Factor (f a)                     -> MultiFactor f '[a]
    CombinedFactors :: Factor Int -> Factor (f a) -> MultiFactor f as -> MultiFactor f (a ': as)


multiFactorIdVector :: MultiFactor f as -> VU.Vector Int
multiFactorIdVector (SingleFactor f)                 = factorIdVector f
multiFactorIdVector (CombinedFactors compressed _ _) = factorIdVector compressed


toFactors :: MultiFactor f as -> HList (Factor :. f) as
toFactors (SingleFactor f)         = Compose f :& HNil
toFactors (CombinedFactors _ f fs) = Compose f :& toFactors fs


fromFactors :: HList (Factor :. f) (a ': as) -> MultiFactor f (a ': as)
fromFactors (f :& HNil)        = SingleFactor (getCompose f)
fromFactors (f :& fs@(_ :& _)) = addFactor (getCompose f) (fromFactors fs)


addFactor :: Factor (f a) -> MultiFactor f as -> MultiFactor f (a ': as)
addFactor f@(Factor lvsA idVecA) fs =
    let compressed = factorizeHashable $
            liftA2 (\idA idAS -> idA + idAS * levelsSize lvsA)
                (indexVector idVecA)
                (indexVector (multiFactorIdVector fs))

    in
        CombinedFactors compressed f fs

