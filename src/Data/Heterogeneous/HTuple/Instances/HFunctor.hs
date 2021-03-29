{-# options_ghc -Wno-orphans -Wno-unused-matches #-}
{-# language TemplateHaskell #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.HTuple.Instances.HFunctor where

import Data.Heterogeneous.Class.HApply
import Data.Heterogeneous.Class.HFunctor
import Data.Heterogeneous.HTuple.TH
import Data.Heterogeneous.HTuple.Types


$(forTH [0..maxInstances] \n -> do
    cxt <- htupleInstanceContext n
    cxt' <- htupleInstanceContext n

    [d|
        instance HFunctor HTuple $(gen_listTy cxt) where
            himap f $(gen_tupPat cxt) =
                $(gen_tupExp cxt \i _ty aE -> [| f $(snatE i) $aE |])

        instance HApply HTuple $(gen_listTy cxt) where
            hizipWith f $(gen_tupPat cxt) $(gen_tupPat cxt') =
                $(gen_tupExp cxt \i _ty aE -> [| f $(snatE i) $aE $(gen_aExps cxt' !! i) |])
      |])
