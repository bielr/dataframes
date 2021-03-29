{-# options_ghc -Wno-orphans -Wno-unused-matches #-}
{-# language TemplateHaskell #-}
{-# language TupleSections #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.HTuple.Instances.HCoerce where

import Data.Type.Coercion

import Data.Heterogeneous.Class.HCoerce
import Data.Heterogeneous.HTuple.TH
import Data.Heterogeneous.HTuple.Types


$(forTH [0..maxInstances] \n -> do
    cxt <- htupleInstanceContext n

    [d|
        instance HCoerce HTuple $(gen_listTy cxt) where
            hliftCoercion co =
                $(foldr
                    (\_ty r -> [| case co of Coercion -> $r |])
                    [| Coercion |]
                    (gen_aTys cxt))
            {-# inline hliftCoercion #-}

            hliftCoercionF _ co =
                $(foldr
                    (\aTy r -> [| case co @($aTy) of Coercion -> $r |])
                    [| Coercion |]
                    (gen_aTys cxt))
            {-# inline hliftCoercionF #-}
      |])
