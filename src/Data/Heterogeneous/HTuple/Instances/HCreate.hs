{-# options_ghc -Wno-orphans -Wno-unused-matches #-}
{-# language TemplateHaskell #-}
{-# language TupleSections #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.HTuple.Instances.HCreate where

import Data.Foldable (foldl')
import Language.Haskell.TH qualified as TH

import Data.Heterogeneous.Class.HCreate
import Data.Heterogeneous.HTuple.TH
import Data.Heterogeneous.HTuple.Types


$(forTH [0..maxInstances] \n -> do
    cxt <- htupleInstanceContext n

    let tupCon = return (TH.TupE (replicate n Nothing))

    [d|
        instance HCreate HTuple $(gen_listTy cxt) where
            hcreateA f =
                fmap HTuple
                    $(foldl'
                        (\ff i -> [e| $ff <*> f $(snatE i) |])
                        [e| pure $tupCon |]
                        [0..n-1])
            {-# inline hcreateA #-}
      |])
