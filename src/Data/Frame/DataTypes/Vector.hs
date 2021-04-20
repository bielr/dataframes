{-# language GeneralizedNewtypeDeriving #-}
{-# language UndecidableInstances #-}
module Data.Frame.DataTypes.Vector
  ( module Data.Frame.DataTypes.VectorMode
  , VectorType
  , MVectorType
  , VectorTypeOf
  , MVectorTypeOf
  , MVector
  , Vector
  ) where

import GHC.Exts (IsList(..))
import Control.Lens qualified as L
import Data.Vector.Generic.Lens (vectorIx)

import Data.Vector                 qualified as VB
import Data.Vector.Generic         qualified as VG
import Data.Vector.Generic.Mutable qualified as VGM
import Data.Vector.Primitive       qualified as VP
import Data.Vector.Storable        qualified as VS
import Data.Vector.Unboxed         qualified as VU

import Data.Frame.Kind
import Data.Frame.DataTypes.VectorMode


type VectorType :: VectorMode -> Type -> Type

type family VectorType vm = v | v -> vm where
    VectorType 'Boxed     = VB.Vector
    VectorType 'Primitive = VP.Vector
    VectorType 'Storable  = VS.Vector
    VectorType 'Unboxed   = VU.Vector


type MVectorType :: VectorMode -> Type -> Type -> Type
type MVectorType vm = VG.Mutable (VectorType vm)


type VectorTypeOf :: Type -> Type -> Type
type VectorTypeOf a = VectorType (VectorModeOf a)

type MVectorTypeOf :: Type -> Type -> Type -> Type
type MVectorTypeOf a = MVectorType (VectorModeOf a)


type MVector :: Type -> Type -> Type
newtype MVector s a = MVector (MVectorTypeOf a s a)

type Vector :: Type -> Type
newtype Vector a = Vector (VectorTypeOf a a)


type instance VG.Mutable Vector = MVector

instance VGM.MVector (MVectorTypeOf a) a => VGM.MVector MVector a where
    basicLength (MVector v)                     = VGM.basicLength v
    basicUnsafeSlice start len (MVector v)      = MVector (VGM.basicUnsafeSlice start len v)
    basicOverlaps (MVector v) (MVector v')      = VGM.basicOverlaps v v'
    basicUnsafeNew len                          = MVector <$> VGM.basicUnsafeNew len
    basicInitialize (MVector v)                 = VGM.basicInitialize v
    basicUnsafeReplicate len !a                 = VGM.basicUnsafeReplicate len a
    basicUnsafeRead (MVector v) i               = VGM.basicUnsafeRead v i
    basicUnsafeWrite (MVector v) i !a           = VGM.basicUnsafeWrite v i a
    basicClear (MVector v)                      = VGM.basicClear v
    basicSet (MVector v) !a                     = VGM.basicSet v a
    basicUnsafeCopy (MVector tgt) (MVector src) = VGM.basicUnsafeCopy tgt src
    basicUnsafeMove (MVector tgt) (MVector src) = VGM.basicUnsafeMove tgt src
    basicUnsafeGrow (MVector v) len             = MVector <$> VGM.basicUnsafeGrow v len


instance VG.Vector (VectorTypeOf a) a => VG.Vector Vector a where
    basicUnsafeFreeze (MVector v)           = Vector <$> VG.basicUnsafeFreeze v
    basicUnsafeThaw (Vector v)              = MVector <$> VG.basicUnsafeThaw v
    basicLength (Vector v)                  = VG.basicLength v
    basicUnsafeSlice start len (Vector v)   = Vector (VG.basicUnsafeSlice start len v)
    basicUnsafeIndexM (Vector v) i          = VG.basicUnsafeIndexM v i
    basicUnsafeCopy (MVector mv) (Vector v) = VG.basicUnsafeCopy mv v
    elemseq (Vector v) a b                  = a `seq` VG.elemseq v a b


instance VG.Vector (VectorTypeOf a) a => IsList (Vector a) where
    type Item (Vector a) = a
    toList = VG.toList
    fromList = VG.fromList
    fromListN = VG.fromListN


type instance L.Index (Vector a) = Int
type instance L.IxValue (Vector a) = a


instance VG.Vector Vector a => L.Ixed (Vector a) where
    ix = vectorIx
