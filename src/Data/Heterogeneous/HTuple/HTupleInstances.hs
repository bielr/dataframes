{-# options_ghc -Wno-orphans -Wno-unused-matches #-}
{-# language TupleSections #-}
{-# language TemplateHaskell #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.HTuple.HTupleInstances () where

import Data.Foldable (foldl')
import Data.Traversable (forM)
import Language.Haskell.TH qualified as TH

import Data.Heterogeneous.Class.HCreate
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.HTuple.HTuple
import Data.Heterogeneous.HTuple.TH
import Data.Heterogeneous.TypeLevel



$(concat <$> forM [0..16] \n -> do
    cxt <- htupleInstanceContext n

    concat <$> forM [0..n-1] \i ->
        [d|
          instance
              a ~ $(gen_aTys cxt !! i)
              => HGetI HTuple a $(gen_listTy cxt) $(peanoTys !! i) where

              hgetC $(gen_tupPat cxt) = $(gen_aExps cxt !! i)
          |])


$(concat <$> forM [0..16] \n -> do
    cxt <- htupleInstanceContext n

    aName <- TH.newName "a"
    let aTy = TH.varT aName

    bName <- TH.newName "b"
    let bTy  = TH.varT bName
        bPat = TH.varP bName
        bVar = TH.varE bName

    cxt2 <- htupleInstanceContext n

    forM [0..n-1] \i -> do
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

            hsetCimpl :: TH.DecQ
            hsetCimpl =
                TH.funD 'hsetC
                    [ TH.clause [TH.bangP bPat, gen_tupPat cxt]
                        (TH.normalB $
                            gen_tupExp cxt \j _ fa ->
                                if j /= i then fa else bVar)
                        []
                    ]


        TH.instanceD (TH.cxt hsetICxtPreds) hsetIinstHead [hsetCimpl])


$(concat <$> forM [0..32] \n -> do
    cxt <- htupleInstanceContext n

    let tupCon = return (TH.TupE (replicate n Nothing))

    [d|
        instance HCreate HTuple $(gen_listTy cxt) where
            hcreateA f = fmap HTuple $(
                foldl' (\ff i -> [e| $ff <*> f (getSNat @($i)) |])
                    [e| pure $tupCon |]
                    (take n peanoTys)
                )
      |])

