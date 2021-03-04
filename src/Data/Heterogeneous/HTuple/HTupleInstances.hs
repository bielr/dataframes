{-# options_ghc -Wno-orphans #-}
{-# language AllowAmbiguousTypes #-}
{-# language QuantifiedConstraints #-}
{-# language TemplateHaskell #-}
{-# language ViewPatterns #-}
module Data.Heterogeneous.HTuple.RTupledInstances () where

import Data.Heterogeneous.RTupled.TH


$(generateRTupledInstancesFromTo 1 62)
