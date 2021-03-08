{-# options_ghc -Wno-orphans -freduction-depth=0 #-}
{-# language AllowAmbiguousTypes #-}
{-# language TemplateHaskell #-}
module Data.Heterogeneous.Constraints.TupledInstances () where

import Data.Heterogeneous.Constraints.TH
import Data.Heterogeneous.Constraints.Tupled
import Data.Heterogeneous.TypeLevel


-- $(generateTupledInstancesFromTo 0 64)
$(generateTupledInstancesFromTo 0 32)


instance {-# overlappable #-} (c, Tupled cs) => Tupled (c ': cs) where
    instAt i r = caseNat i r (instAt @cs (predNat i) r)
