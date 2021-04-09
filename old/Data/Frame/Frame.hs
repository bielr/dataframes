{-# language GADTs #-}
{-# language PatternSynonyms #-}
{-# language QuantifiedConstraints #-}
{-# language StrictData #-}
{-# language UndecidableInstances #-}
{-# language ViewPatterns #-}
module Data.Frame.Frame
  ( Frame
  , pattern ByRows
  , pattern ByCols
  , frameRows
  , frameCols
  , nrows
  , colwise
  , rowwise
  , indexFrame
  , forceFrame
  ) where

import Control.Lens.Type

import Data.Frame.Internal.Column (Col)
import Data.Frame.Internal.Frame
import Data.Frame.Internal.Repr


frameCols :: Getter (Frame rep 'Cols rec cols) (rec (Col rep) cols)
frameCols = colsRec
