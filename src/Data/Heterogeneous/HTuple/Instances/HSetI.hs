{-# options_ghc -Wno-orphans -Wno-unused-matches #-}
{-# language TemplateHaskell #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.HTuple.Instances.HSetI where

import Language.Haskell.TH qualified as TH

import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.HTuple.TH
import Data.Heterogeneous.HTuple.Types

import Data.Heterogeneous.HTuple.Instances.HGetI ()


$(forTH [0..maxInstances] \n -> do
    cxt <- htupleInstanceContext n

    aName <- TH.newName "a"
    let aTy = TH.varT aName

    bName <- TH.newName "b"
    let bTy  = TH.varT bName
        bPat = TH.varP bName
        bVar = TH.varE bName

    cxt2 <- htupleInstanceContext n

    forTH [0..n-1] \i -> do
        let hsetICxtPreds :: [TH.PredQ]
            hsetICxtPreds =
              [t| $aTy ~ $(gen_aTys cxt !! i) |]
              :
              [ if j /= i
                  then [t| $(gen_aTys cxt !! j) ~ $(gen_aTys cxt2 !! j) |]
                  else [t| $bTy ~ $(gen_aTys cxt2 !! j) |]
              | j <- [0..n-1]
              ]

            hsetIinstHead :: TH.TypeQ
            hsetIinstHead =
              [t| HSetI HTuple $aTy $bTy $(gen_listTy cxt) $(gen_listTy cxt2) $(peanoTys !! i) |]

            hsetIimpl :: TH.DecQ
            hsetIimpl =
                TH.funD 'hsetI
                    [ TH.clause [TH.bangP bPat, gen_tupPat cxt]
                        (TH.normalB $
                            gen_tupExp cxt \j _ fa ->
                                if j /= i then fa else bVar)
                        []
                    ]

        fmap (:[]) $
            TH.instanceD (TH.cxt hsetICxtPreds) hsetIinstHead [hsetIimpl])
