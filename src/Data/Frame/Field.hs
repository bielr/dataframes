{-# language DeriveGeneric #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language RoleAnnotations #-}
{-# language UndecidableInstances #-}
module Data.Frame.Field
  ( Field(..)
  , untagged
  , renamed
  , renamedTo
  ) where

import GHC.Generics (Generic)
import Foreign.Storable (Storable)

import Control.Lens.Type
import qualified Control.Lens as L

import qualified Data.Vector.Generic         as VG
import qualified Data.Vector.Generic.Mutable as VGM
import qualified Data.Vector.Unboxed         as VU

import Data.Vinyl.TypeLevel (Snd)
import qualified Data.Vinyl.XRec as VX

import Data.Frame.Kind


newtype Field (tag :: FieldK) = Field { getField :: Snd tag }
    deriving (Generic)


deriving instance Eq (Snd tag) => Eq (Field tag)
deriving instance Ord (Snd tag) => Ord (Field tag)
deriving instance Show (Snd tag) => Show (Field tag)

deriving instance Storable (Snd tag) => Storable (Field tag)


newtype instance VU.Vector (Field col) = FieldVec (VU.Vector (Snd col))
newtype instance VU.MVector s (Field col) = FieldMVec (VU.MVector s (Snd col))

instance VGM.MVector VU.MVector (Snd col) => VGM.MVector VU.MVector (Field col) where
    basicLength (FieldMVec v)                       = VGM.basicLength v
    basicUnsafeSlice start len (FieldMVec v)        = FieldMVec $ VGM.basicUnsafeSlice start len v
    basicOverlaps (FieldMVec v) (FieldMVec v')      = VGM.basicOverlaps v v'
    basicUnsafeNew len                              = FieldMVec <$> VGM.basicUnsafeNew len
    basicInitialize (FieldMVec v)                   = VGM.basicInitialize v
    basicUnsafeReplicate len (Field a)              = FieldMVec <$> VGM.basicUnsafeReplicate len a
    basicUnsafeRead (FieldMVec v) i                 = Field <$> VGM.basicUnsafeRead v i
    basicUnsafeWrite (FieldMVec v) i (Field a)      = VGM.basicUnsafeWrite v i a
    basicClear (FieldMVec v)                        = VGM.basicClear v
    basicSet (FieldMVec v) (Field a)                = VGM.basicSet v a
    basicUnsafeCopy (FieldMVec tgt) (FieldMVec src) = VGM.basicUnsafeCopy tgt src
    basicUnsafeMove (FieldMVec tgt) (FieldMVec src) = VGM.basicUnsafeMove tgt src
    basicUnsafeGrow (FieldMVec v) len               = FieldMVec <$> VGM.basicUnsafeGrow v len


instance VG.Vector VU.Vector (Snd col) => VG.Vector VU.Vector (Field col) where
    basicUnsafeFreeze (FieldMVec v)             = FieldVec <$> VG.basicUnsafeFreeze v
    basicUnsafeThaw (FieldVec v)                = FieldMVec <$> VG.basicUnsafeThaw v
    basicLength (FieldVec v)                    = VG.basicLength v
    basicUnsafeSlice start len (FieldVec v)     = FieldVec $ VG.basicUnsafeSlice start len v
    basicUnsafeIndexM (FieldVec v) i            = Field <$> VG.basicUnsafeIndexM v i
    basicUnsafeCopy (FieldMVec mv) (FieldVec v) = VG.basicUnsafeCopy mv v
    elemseq (FieldVec v) (Field a) b            = VG.elemseq v a b


instance VU.Unbox (Snd col) => VU.Unbox (Field col)


instance VX.IsoHKD Field col where
    type HKD Field col = Snd col

    unHKD = Field
    toHKD = getField


untagged :: forall s a b. Iso (Field '(s, a)) (Field '(s, b)) a b
untagged = L.coerced
{-# inline untagged #-}


renamed :: forall s t a. Iso' (Field '(s, a)) (Field '(t, a))
renamed = L.coerced
{-# inline renamed #-}


renamedTo :: forall t s a. Iso' (Field '(s, a)) (Field '(t, a))
renamedTo = L.coerced
{-# inline renamedTo #-}
