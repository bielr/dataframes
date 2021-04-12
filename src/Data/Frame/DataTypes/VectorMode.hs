{-# language GeneralizedNewtypeDeriving #-}
{-# language DeriveGeneric #-}
{-# language UndecidableInstances #-}
module Data.Frame.DataTypes.VectorMode
  ( VectorMode(..)
  , SVectorMode(..)
  , KnownVectorMode(..)
  , MeetVectorMode
  , WithVectorMode(..)
  , VectorModeOf
  ) where

import GHC.Generics (Generic)
import GHC.Tuple (Solo)

import Data.Hashable (Hashable)
import Data.ByteString             qualified as BS
import Data.ByteString.Short       qualified as BS
import Data.ByteString.Lazy        qualified as BL
import Data.Int
import Data.Text (Text)
import Data.Vector                 qualified as VB
import Data.Vector.Generic         qualified as VG
import Data.Vector.Generic.Mutable qualified as VGM
import Data.Vector.Primitive       qualified as VP
import Data.Vector.Unboxed         qualified as VU
import Data.Vector.Storable        qualified as VS
import Data.Word

import Foreign.Storable (Storable)

import Data.Frame.Kind


data VectorMode = Boxed | Primitive | Unboxed | Storable


-- Singletons code

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


-- Combining VectorMode's

type MeetVectorMode :: VectorMode -> VectorMode -> VectorMode

-- Primitive < Unboxed < Storable < Boxed
type family MeetVectorMode vm1 vm2 where
    MeetVectorMode 'Primitive 'Unboxed   = 'Unboxed
    MeetVectorMode 'Primitive 'Storable  = 'Storable
    MeetVectorMode 'Primitive 'Boxed     = 'Boxed

    MeetVectorMode 'Unboxed   'Storable  = 'Storable
    MeetVectorMode 'Unboxed   'Boxed     = 'Boxed

    MeetVectorMode 'Storable  'Boxed     = 'Boxed

    MeetVectorMode vm         vm         = vm
    MeetVectorMode vm1        vm2        = MeetVectorMode vm2 vm1


-- utility to manually select a vector mode instead of providing an instance
type WithVectorMode :: VectorMode -> Type -> Type
newtype WithVectorMode vm a = WithVectorMode a
    deriving newtype (Eq, Ord, Show, Hashable, Storable)
    deriving stock Generic


newtype instance VU.MVector s (WithVectorMode vm a) = WithVectorModeMVector (VU.MVector s a)

instance VGM.MVector VU.MVector a => VGM.MVector VU.MVector (WithVectorMode vm a) where
    basicLength (WithVectorModeMVector v)                                   = VGM.basicLength v
    basicUnsafeSlice start len (WithVectorModeMVector v)                    = WithVectorModeMVector $ VGM.basicUnsafeSlice start len v
    basicOverlaps (WithVectorModeMVector v) (WithVectorModeMVector v')      = VGM.basicOverlaps v v'
    basicUnsafeNew len                                                      = WithVectorModeMVector <$> VGM.basicUnsafeNew len
    basicInitialize (WithVectorModeMVector v)                               = VGM.basicInitialize v
    basicUnsafeReplicate len (WithVectorMode a)                             = WithVectorModeMVector <$> VGM.basicUnsafeReplicate len a
    basicUnsafeRead (WithVectorModeMVector v) i                             = WithVectorMode <$> VGM.basicUnsafeRead v i
    basicUnsafeWrite (WithVectorModeMVector v) i (WithVectorMode a)         = VGM.basicUnsafeWrite v i a
    basicClear (WithVectorModeMVector v)                                    = VGM.basicClear v
    basicSet (WithVectorModeMVector v) (WithVectorMode a)                   = VGM.basicSet v a
    basicUnsafeCopy (WithVectorModeMVector tgt) (WithVectorModeMVector src) = VGM.basicUnsafeCopy tgt src
    basicUnsafeMove (WithVectorModeMVector tgt) (WithVectorModeMVector src) = VGM.basicUnsafeMove tgt src
    basicUnsafeGrow (WithVectorModeMVector v) len                           = WithVectorModeMVector <$> VGM.basicUnsafeGrow v len

newtype instance VU.Vector (WithVectorMode vm a)  = WithVectorModeVector (VU.Vector a)

instance VG.Vector VU.Vector a => VG.Vector VU.Vector (WithVectorMode vm a) where
    basicUnsafeFreeze (WithVectorModeMVector v)                         = WithVectorModeVector <$> VG.basicUnsafeFreeze v
    basicUnsafeThaw (WithVectorModeVector v)                            = WithVectorModeMVector <$> VG.basicUnsafeThaw v
    basicLength (WithVectorModeVector v)                                = VG.basicLength v
    basicUnsafeSlice start len (WithVectorModeVector v)                 = WithVectorModeVector $ VG.basicUnsafeSlice start len v
    basicUnsafeIndexM (WithVectorModeVector v) i                        = WithVectorMode <$> VG.basicUnsafeIndexM v i
    basicUnsafeCopy (WithVectorModeMVector mv) (WithVectorModeVector v) = VG.basicUnsafeCopy mv v
    elemseq (WithVectorModeVector v) (WithVectorMode a) b               = VG.elemseq v a b


instance VU.Unbox a => VU.Unbox (WithVectorMode vm a)


-- Automatically selecting the appropriate vector mode for any supported type

type VectorModeOf :: Type -> VectorMode

type family VectorModeOf a
type instance VectorModeOf (WithVectorMode vm a) = vm
type instance VectorModeOf ()                    = 'Unboxed
type instance VectorModeOf Bool                  = 'Unboxed
type instance VectorModeOf Char                  = 'Unboxed
type instance VectorModeOf Double                = 'Unboxed
type instance VectorModeOf Float                 = 'Unboxed
type instance VectorModeOf Int                   = 'Unboxed
type instance VectorModeOf Int8                  = 'Unboxed
type instance VectorModeOf Int16                 = 'Unboxed
type instance VectorModeOf Int32                 = 'Unboxed
type instance VectorModeOf Int64                 = 'Unboxed
type instance VectorModeOf Word                  = 'Unboxed
type instance VectorModeOf Word8                 = 'Unboxed
type instance VectorModeOf Word16                = 'Unboxed
type instance VectorModeOf Word32                = 'Unboxed
type instance VectorModeOf Word64                = 'Unboxed
type instance VectorModeOf (a -> b)              = 'Boxed
type instance VectorModeOf (Maybe a)             = 'Boxed
type instance VectorModeOf (Either a b)          = 'Boxed
type instance VectorModeOf [a]                   = 'Boxed
type instance VectorModeOf Text                  = 'Boxed
type instance VectorModeOf BS.ByteString         = 'Boxed
type instance VectorModeOf BL.ByteString         = 'Boxed
type instance VectorModeOf BS.ShortByteString    = 'Boxed
type instance VectorModeOf (VB.Vector a)         = 'Boxed
type instance VectorModeOf (VP.Vector a)         = 'Boxed
type instance VectorModeOf (VU.Vector a)         = 'Boxed
type instance VectorModeOf (VS.Vector a)         = 'Boxed
type instance VectorModeOf (Solo a)              = VectorModeOf a
type instance VectorModeOf (a,b)                 = RelaxVectorMode 'Unboxed '[a,b]
type instance VectorModeOf (a,b,c)               = RelaxVectorMode 'Unboxed '[a,b,c]
type instance VectorModeOf (a,b,c,d)             = RelaxVectorMode 'Unboxed '[a,b,c,d]
type instance VectorModeOf (a,b,c,d,e)           = RelaxVectorMode 'Unboxed '[a,b,c,d,e]
type instance VectorModeOf (a,b,c,d,e,f)         = RelaxVectorMode 'Unboxed '[a,b,c,d,e,f]


type RelaxVectorMode :: VectorMode -> [Type] -> VectorMode
type family RelaxVectorMode def vms where
    RelaxVectorMode def '[]       = def
    RelaxVectorMode def (a ': as) = RelaxVectorMode (MeetVectorMode def (VectorModeOf a)) as

