{-# language QuasiQuotes #-}
{-# language DerivingStrategies #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Data.Frame.TH where

import Language.Haskell.TH

import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VGM

import Data.Frame.Vectors (ColVector, ColMVector)
import qualified Data.Vinyl.XRec as VX


instanceColVectorQ :: TypeQ -> TypeQ -> DecsQ
instanceColVectorQ vecTypeQ colTypeQ = do
    colType_ <- colTypeQ
    let colType = return colType_

    vecType_ <- vecTypeQ
    let vecType = return vecType_

    [d|
        newtype instance ColVector    $colType = MkColVector  ($vecType $colType)
        newtype instance ColMVector s $colType = MkColMVector (VG.Mutable $vecType s $colType)

        instance VGM.MVector ColMVector $colType where
            basicLength (MkColMVector v)                          = VGM.basicLength v
            basicUnsafeSlice start len (MkColMVector v)           = MkColMVector (VGM.basicUnsafeSlice start len v)
            basicOverlaps (MkColMVector v) (MkColMVector v')      = VGM.basicOverlaps v v'
            basicUnsafeNew len                                    = fmap MkColMVector (VGM.basicUnsafeNew len)
            basicInitialize (MkColMVector v)                      = VGM.basicInitialize v
            basicUnsafeReplicate len a                            = fmap MkColMVector (VGM.basicUnsafeReplicate len a)
            basicUnsafeRead (MkColMVector v) i                    = VGM.basicUnsafeRead v i
            basicUnsafeWrite (MkColMVector v) i                   = VGM.basicUnsafeWrite v i
            basicClear (MkColMVector v)                           = VGM.basicClear v
            basicSet (MkColMVector v) a                           = VGM.basicSet v a
            basicUnsafeCopy (MkColMVector tgt) (MkColMVector src) = VGM.basicUnsafeCopy tgt src
            basicUnsafeMove (MkColMVector tgt) (MkColMVector src) = VGM.basicUnsafeMove tgt src
            basicUnsafeGrow (MkColMVector v) len                  = fmap MkColMVector (VGM.basicUnsafeGrow v len)

        instance VG.Vector ColVector $colType where
            basicUnsafeFreeze (MkColMVector v)                    = fmap MkColVector (VG.basicUnsafeFreeze v)
            basicUnsafeThaw (MkColVector v)                       = fmap MkColMVector (VG.basicUnsafeThaw v)
            basicLength (MkColVector v)                           = VG.basicLength v
            basicUnsafeSlice start len (MkColVector v)            = MkColVector (VG.basicUnsafeSlice start len v)
            basicUnsafeIndexM (MkColVector v) i                   = VG.basicUnsafeIndexM v i
            basicUnsafeCopy (MkColMVector mv) (MkColVector v)     = VG.basicUnsafeCopy mv v
            elemseq (MkColVector v) a b                           = VG.elemseq v a b

        instance VX.IsoHKD ColVector $colType where
            type HKD ColVector $colType = $vecType $colType
            toHKD (MkColVector v) = v
            unHKD = MkColVector
        |]

instanceColVector :: Name -> Name -> DecsQ
instanceColVector vecTypeName colTypeName =
    instanceColVectorQ (conT vecTypeName) (conT colTypeName)
