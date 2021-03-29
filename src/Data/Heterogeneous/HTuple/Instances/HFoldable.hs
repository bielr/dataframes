{-# options_ghc -Wno-orphans -Wno-unused-matches #-}
{-# language TemplateHaskell #-}
{-# language TupleSections #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.HTuple.Instances.HFoldable where

import Data.Heterogeneous.Class.HFoldable
import Data.Heterogeneous.HTuple.TH
import Data.Heterogeneous.HTuple.Types


$(forTH [0..maxInstances] \n -> do
    cxt <- htupleInstanceContext n
    cxt' <- htupleInstanceContext n

    [d|
        instance HFoldable HTuple $(gen_listTy cxt) where
            hifoldr f z $(gen_tupPat cxt) =
                $(foldr
                    (\(i, aE) r -> [| f $(snatE i) $aE $r |])
                    [| z |]
                    (zip [0..] (gen_aExps cxt)))
            {-# inline hifoldr #-}

            hifoldr2 f z $(gen_tupPat cxt) $(gen_tupPat cxt') =
                $(foldr
                    (\(i, aE, bE) r -> [| f $(snatE i) $aE $bE $r |])
                    [| z |]
                    (zip3 [0..] (gen_aExps cxt) (gen_aExps cxt')))
            {-# inline hifoldr2 #-}
      |])
