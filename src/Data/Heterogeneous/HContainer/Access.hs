{-# language AllowAmbiguousTypes #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.HContainer.Access where

import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.TypeLevel.Subseq


type GetElemI :: forall k. HTyCon k -> k -> [k] -> Peano -> Constraint


class i ~ IndexOf r rs => GetElemI hf r rs i | i r -> rs, rs i -> r where
    hgetC :: hf f rs -> f r


class
    ( GetElemI hf r rs i
    , GetElemI hf r' rs' i
    , ReplaceSubseq '[r] '[r'] rs rs' '[i]
    )
    => SetElemI hf r r' rs rs' i where
    hputC :: f r' -> hf f rs -> hf f rs'

    hlensC :: Functor g => (f r -> g (f r')) -> hf f rs -> g (hf f rs')

-- instance Vy.GetElemI Rec r r' rs rs' (RIndex r rs) => GetElemI Rec r r' rs rs' where
--     hgetC = Vy.hgetC
--     hputC = Vy.hputC @Rec @r
--     hlensC = Vy.hlensC
--
--
-- instance Vy.GetElemI ARec r r' rs rs' (RIndex r rs) => GetElemI ARec r r' rs rs' where
--     hgetC = Vy.hgetC
--     hputC = Vy.hputC @ARec @r
--     hlensC = Vy.hlensC
--
--
-- instance Vy.GetElemI SARec r r' rs rs' (RIndex r rs) => GetElemI SARec r r' rs rs' where
--     hgetC = Vy.hgetC
--     hputC = Vy.hputC @SARec @r
--     hlensC = Vy.hlensC


hget :: forall r rs f hf.  GetElemI hf r rs (IndexOf r rs) => hf f rs -> f r
hget = hgetC


hput :: forall r r' rs rs' f hf.
    SetElemI hf r r' rs rs' (IndexOf r rs)
    => f r' -> hf f rs -> hf f rs'
hput = hputC


hlens :: forall r r' rs rs' f g hf.
    (Functor g, SetElemI hf r r' rs rs' (IndexOf r rs))
    => (f r -> g (f r'))
    -> hf f rs -> g (hf f rs')
hlens = hlensC
