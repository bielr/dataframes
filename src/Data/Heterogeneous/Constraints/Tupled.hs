{-# language AllowAmbiguousTypes #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
module Data.Heterogeneous.Constraints.Tupled where

import Data.Heterogeneous.TypeLevel


type FoldConstraints :: [Constraint] -> Constraint

type family FoldConstraints cs = r | r -> cs where
    FoldConstraints '[]       = ()
    FoldConstraints (c ': cs) = (c, FoldConstraints cs)


type Tupled :: [Constraint] -> Constraint

class FoldConstraints cs => Tupled cs where
    instAt :: i < Length cs => SNat i -> (cs !! i => r) -> r
