{-# language AllowAmbiguousTypes #-}
{-# language DeriveGeneric #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language UndecidableInstances #-}
module Data.Frame.Dplyr
  ( module Exports
  ) where

import Data.Frame.Dplyr.Basic as Exports
import Data.Frame.Dplyr.Group as Exports
import Data.Frame.Dplyr.Index as Exports
import Data.Frame.Dplyr.Row   as Exports
import Data.Frame.VinylExts   as Exports (RMonoid(..), RSingleton(..))
