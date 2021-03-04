{-# language QuantifiedConstraints #-}
module Data.Heterogeneous.Roles where

--import Data.Coerce
import Data.Type.Coercion


-- Proof that a record is representational on f

class RRepresentational rec where
    rrepF :: Coercion f g -> Coercion (rec f as) (rec g as)

--instance (forall f g. Coercible f g => Coercible (rec f) (rec g)) => RRepresentational rec

-- Proof that a record is phantom on f

-- class (forall f g. Coercible (rec f) (rec g)) => RPhantom rec
-- instance (forall f g. Coercible (rec f) (rec g)) => RPhantom rec
