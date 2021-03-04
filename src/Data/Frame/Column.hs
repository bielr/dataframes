{-# language DeriveFunctor #-}
module Data.Frame.Column
  ( ColType
  , ColTypes
  , Col
  , ColRepF
  , indexCol
  , forceCol
  , fromCol
  , HasFields(..)
  , ColIx(..)
  , withDF
  , colIx
  , runColIx
  ) where

import Data.Coerce
import Data.Profunctor.Unsafe
import Data.Vector.Generic qualified as VG
import Data.Vinyl.TypeLevel (Snd)

import Data.Indexer

import Data.Frame.Field
import Data.Frame.Internal.Frame (Frame(..), nrows)
import Data.Frame.Kind
import Data.Frame.Internal.Column
import Data.Frame.Internal.Repr


newtype ColIx df a = ColIx (df -> Int -> a)
    deriving (Functor)


instance Applicative (ColIx df) where
    pure a = ColIx \_ _ -> a

    ColIx dfixf <*> ColIx dfixa = ColIx \df ->
        let !ixf = dfixf df
            !ixa = dfixa df
        in ixf <*> ixa


instance Profunctor ColIx where
    dimap l r (ColIx dfia) = ColIx ((r .) . dfia . l)
    rmap r (ColIx dfia) = ColIx ((r .) . dfia)
    lmap l (ColIx dfia) = ColIx (dfia . l)

    r #. ColIx dfia = ColIx ((r #.) #. dfia)
    ColIx dfia .# l = ColIx (dfia .# l)


withDF :: (df -> a) -> ColIx df a
withDF f = ColIx \df ->
    let !a = f df
    in const a


colIx :: When (rep == 'Vec) (ColType col) => Col rep col -> Int -> Snd col
colIx = \case
    ColVec v             -> coerce (v VG.!)
    ColGen (Indexer _ a) -> coerce a


runColIx :: forall col' s a rep by rec cols.
    ( When (rep == 'Vec) (ColType col')
    , col' ~ '(s, a)
    )
    => Frame rep by rec cols -> ColIx (Frame rep by rec cols) a -> Col rep '(s, a)
runColIx df (ColIx dfixa) =
    let !g = dfixa df
    in
        case df of
          RowsVec _   -> generateCol $ Indexer (nrows df) g
          RowsGen _   -> generateCol $ Indexer (nrows df) g
          ColVecs _ _ -> generateCol $ Indexer (nrows df) g
          ColGens _ _ -> generateCol $ Indexer (nrows df) g
