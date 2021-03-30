module Data.Frame.Dplyr.Ops
  ( (&)
  , module LensOps
  , Rec(..)
  , (=:)
  , (=:=)
  , type (:::)
  , type (++)
  , (|.)
  ) where


import Data.Function ((&))

import Control.Lens.Combinators as LensOps (view, to, over)
import Control.Lens.Operators   as LensOps ((^.), (#), (.~), (%~), (%%~), (<.), (.>))

import Data.Vinyl (Rec(..))
import Data.Vinyl.Derived (type (:::), (=:), (=:=))
import Data.Vinyl.TypeLevel (type (++))


(|.) :: (a -> b) -> (b -> c) -> a -> c
f |. g = g . f
{-# inline (|.) #-}

infixl 3 |.
