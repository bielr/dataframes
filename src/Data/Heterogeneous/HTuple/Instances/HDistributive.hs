{-# options_ghc -Wno-orphans -Wno-unused-matches #-}
{-# language TemplateHaskell #-}
{-# language TupleSections #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.HTuple.Instances.HDistributive where

import Data.Heterogeneous.Class.HDistributive
import Data.Heterogeneous.HTuple.TH
import Data.Heterogeneous.HTuple.Types

import Data.Heterogeneous.HTuple.Instances.HFunctor ()


$(forTH [0..maxInstances] \n -> do
    cxt <- htupleInstanceContext n
    cxt' <- htupleInstanceContext n

    [d|
        instance HDistributive HTuple $(gen_listTy cxt) where
            hcotraverse f gtup =
                $(gen_tupExp cxt \i _ty aE ->
                    [| f (fmap (\ $(gen_tupPat cxt) -> $aE) gtup) |])
            {-# inline hcotraverse #-}

            hicotraverse f gtup =
                $(gen_tupExp cxt \i _ty aE ->
                    [| f $(snatE i) (fmap (\ $(gen_tupPat cxt) -> $aE) gtup) |])
            {-# inline hicotraverse #-}
      |])
