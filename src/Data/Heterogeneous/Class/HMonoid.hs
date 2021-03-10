module Data.Heterogeneous.Class.HMonoid where

import Control.Lens (Iso, review)

import Data.Heterogeneous.TypeLevel


-- Class for any record that can be constructed from a single element

type HSingleton :: forall k. HTyConK k -> Constraint

class HSingleton hf where
    hsingleton :: Iso (hf f '[a]) (hf f '[b]) (f a) (f b)


-- Generic monoid-like (for list-like instances) structure

class HMonoid hf where
    hempty :: hf f '[]
    happend :: hf f as -> hf f bs -> hf f (as ++ bs)

    hcons :: f a -> hf f as -> hf f (a ': as)
    hsnoc :: hf f as -> f a -> hf f (as ++ '[a])

    default hcons :: HSingleton hf => f a -> hf f as -> hf f (a ': as)
    hcons = happend . review hsingleton
    {-# inline hcons #-}

    default hsnoc :: HSingleton hf => hf f as -> f a -> hf f (as ++ '[a])
    hsnoc hf fa = happend hf (review hsingleton fa)
    {-# inline hsnoc #-}

