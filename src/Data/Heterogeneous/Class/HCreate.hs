module Data.Heterogeneous.Class.HCreate
  ( HCreate(..)
  , hcreate
  , hnew
  , hnewA
  , hdict
  ) where

import Data.Profunctor.Unsafe ((#.))

import Data.Heterogeneous.Constraints
import Data.Heterogeneous.Functors
import Data.Heterogeneous.TypeLevel


-- Generic record creation

type HCreate :: forall {k}. HTyConK k -> [k] -> Constraint

class HCreate hf as where
    hcreateA ::
        Applicative g
        => (forall i. i < Length as => SNat i -> g (f (as !! i)))
        -> g (hf f as)


hcreate :: forall hf as f.
    HCreate hf as
    => (forall i. i < Length as => SNat i -> f (as !! i))
    -> hf f as
hcreate f = runIdentity (hcreateA (Identity #. f))
{-# inline hcreate #-}


hnew :: forall hf as f. HCreate hf as => (forall a. f a) -> hf f as
hnew fa = runIdentity (hnewA (Identity fa))
{-# inline hnew #-}


hnewA :: forall hf as f g.
    (HCreate hf as, Applicative g)
    => (forall a. g (f a))
    -> g (hf f as)
hnewA gfa = hcreateA (const gfa)
{-# inline hnewA #-}


hdict :: forall c as hf. (HCreate hf as, All c as) => hf (Dict :. c) as
hdict = hcreate (constrained @c @as (Compose Dict))
{-# inline hdict #-}
