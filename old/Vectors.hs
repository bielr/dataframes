module Data.Frame.Vectors where

import qualified Data.Vector.Generic as VG

import Data.Frame.Kind


-- class RecVec (rec :: RecK) (cols :: FieldsK) where
--     allocRec   :: PrimMonad m => Int -> m (ColMVectors m rec cols)
--     freezeRec  :: PrimMonad m => Int -> ColMVectors m rec cols -> m (ColVectors rec cols)
--     growRec    :: PrimMonad m => ColMVectors m rec cols -> m (ColMVectors m rec cols)
--     writeRec   :: PrimMonad m => Int -> ColMVectors m rec cols -> rec Field cols -> m ()
--
--     indexRec   :: Int -> ColVectors rec cols -> rec Field cols
