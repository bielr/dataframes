{-# language UndecidableInstances #-}
module Data.Frame.Internal.ColVector where

import Control.Lens qualified as L
import Data.Vector.Generic.Lens (vectorIx)

import Data.Vector                 qualified as VB
import Data.Vector.Generic         qualified as VG
import Data.Vector.Generic.Mutable qualified as VGM
import Data.Vector.Primitive       qualified as VP
import Data.Vector.Storable        qualified as VS
import Data.Vector.Unboxed         qualified as VU

import Data.Frame.Field
import Data.Frame.Kind


data VectorMode = Boxed | Primitive | Unboxed | Storable


type SVectorMode :: VectorMode -> Type

data SVectorMode vm where
    SBoxed     :: SVectorMode 'Boxed
    SPrimitive :: SVectorMode 'Primitive
    SStorable  :: SVectorMode 'Storable
    SUnboxed   :: SVectorMode 'Unboxed


type KnownVectorMode :: VectorMode -> Constraint

class KnownVectorMode vm where
    sVectorMode :: SVectorMode vm

instance KnownVectorMode 'Boxed      where sVectorMode = SBoxed
instance KnownVectorMode 'Primitive  where sVectorMode = SPrimitive
instance KnownVectorMode 'Storable   where sVectorMode = SStorable
instance KnownVectorMode 'Unboxed    where sVectorMode = SUnboxed


type VectorModeOf :: Type -> VectorMode
type family VectorModeOf a
type instance VectorModeOf (Field col) = VectorModeOf (FieldType col)
type instance VectorModeOf Bool        = 'Unboxed
type instance VectorModeOf Char        = 'Unboxed
type instance VectorModeOf Int         = 'Unboxed
type instance VectorModeOf Float       = 'Unboxed
type instance VectorModeOf Double      = 'Unboxed
type instance VectorModeOf [a]         = 'Boxed


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


type ColMVector :: Type -> Type -> Type
newtype ColMVector s a = ColMVector (MVectorTypeOf a s a)

type ColVector :: Type -> Type
newtype ColVector a = ColVector (VectorTypeOf a a)


type instance VG.Mutable ColVector = ColMVector


instance VGM.MVector (MVectorTypeOf a) a => VGM.MVector ColMVector a where
    basicLength (ColMVector v)                        = VGM.basicLength v
    basicUnsafeSlice start len (ColMVector v)         = ColMVector (VGM.basicUnsafeSlice start len v)
    basicOverlaps (ColMVector v) (ColMVector v')      = VGM.basicOverlaps v v'
    basicUnsafeNew len                                = ColMVector <$> VGM.basicUnsafeNew len
    basicInitialize (ColMVector v)                    = VGM.basicInitialize v
    basicUnsafeReplicate len a                        = ColMVector <$> VGM.basicUnsafeReplicate len a
    basicUnsafeRead (ColMVector v) i                  = VGM.basicUnsafeRead v i
    basicUnsafeWrite (ColMVector v) i                 = VGM.basicUnsafeWrite v i
    basicClear (ColMVector v)                         = VGM.basicClear v
    basicSet (ColMVector v) a                         = VGM.basicSet v a
    basicUnsafeCopy (ColMVector tgt) (ColMVector src) = VGM.basicUnsafeCopy tgt src
    basicUnsafeMove (ColMVector tgt) (ColMVector src) = VGM.basicUnsafeMove tgt src
    basicUnsafeGrow (ColMVector v) len                = ColMVector <$> VGM.basicUnsafeGrow v len


instance VG.Vector (VectorTypeOf a) a => VG.Vector ColVector a where
    basicUnsafeFreeze (ColMVector v)              = fmap ColVector (VG.basicUnsafeFreeze v)
    basicUnsafeThaw (ColVector v)                 = fmap ColMVector (VG.basicUnsafeThaw v)
    basicLength (ColVector v)                     = VG.basicLength v
    basicUnsafeSlice start len (ColVector v)      = ColVector (VG.basicUnsafeSlice start len v)
    basicUnsafeIndexM (ColVector v) i             = VG.basicUnsafeIndexM v i
    basicUnsafeCopy (ColMVector mv) (ColVector v) = VG.basicUnsafeCopy mv v
    elemseq (ColVector v) a b                     = VG.elemseq v a b


type instance L.Index (ColVector a) = Int
type instance L.IxValue (ColVector a) = a


instance VG.Vector ColVector a => L.Ixed (ColVector a) where
    ix = vectorIx
