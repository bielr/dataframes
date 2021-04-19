{-# options_ghc -Wno-orphans -Wno-unused-matches #-}
{-# language TemplateHaskell #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.HTuple.Instances.HGetI where

import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.HTuple.TH
import Data.Heterogeneous.HTuple.Types


$(forTH [0..maxInstances] \n -> do
    cxt <- htupleInstanceContext n

    forTH [0..n-1] \i ->
        [d|
          instance HGetI HTuple $(gen_listTy cxt) $(peanoTys !! i) where
              hgetI $(gen_tupPat cxt) = $(gen_aExps cxt !! i)
              {-# inline hgetI #-}
          |])
