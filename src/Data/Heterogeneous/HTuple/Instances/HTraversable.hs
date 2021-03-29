{-# options_ghc -Wno-orphans -Wno-unused-matches #-}
{-# language TemplateHaskell #-}
{-# language TupleSections #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.HTuple.Instances.HTraversable where

import Data.Foldable (foldl')
import Language.Haskell.TH qualified as TH

import Data.Heterogeneous.Class.HTraversable
import Data.Heterogeneous.HTuple.TH
import Data.Heterogeneous.HTuple.Types

import Data.Heterogeneous.HTuple.Instances.HFoldable ()
import Data.Heterogeneous.HTuple.Instances.HFunctor ()


$(forTH [0..maxInstances] \n -> do
    cxt <- htupleInstanceContext n
    cxt' <- htupleInstanceContext n

    let tupCon = return (TH.TupE (replicate n Nothing))

    [d|
        instance HTraversable HTuple $(gen_listTy cxt) where
            hitraverse f $(gen_tupPat cxt) =
                fmap HTuple $
                    $(foldl'
                        (\ff (i, aE) -> [| $ff <*> f $(snatE i) $aE |])
                        [| pure $tupCon |]
                        (zip [0..] (gen_aExps cxt)))
            {-# inline hitraverse #-}

            hitraverse2 f $(gen_tupPat cxt) $(gen_tupPat cxt') =
                fmap HTuple $
                    $(foldl'
                        (\ff (i, aE, bE) -> [| $ff <*> f $(snatE i) $aE $bE |])
                        [| pure $tupCon |]
                        (zip3 [0..] (gen_aExps cxt) (gen_aExps cxt')))
            {-# inline hitraverse2 #-}
      |])
