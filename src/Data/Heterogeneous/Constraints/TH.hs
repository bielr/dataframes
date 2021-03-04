{-# language QuasiQuotes #-}
{-# language TemplateHaskell #-}
module Data.Heterogeneous.Constraints.TH
  ( generateTupledInstance
  , generateTupledInstancesFromTo
  ) where

import Control.Monad
import Data.Type.Equality

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Data.Heterogeneous.Constraints.Tupled
import Data.Heterogeneous.TypeLevel

import Unsafe.Coerce


peanoLit :: Int -> TypeQ
peanoLit 0 = [t| 'Zero |]
peanoLit n = [t| 'Succ $(peanoLit (n-1)) |]


generateTupledInstance :: Int -> Q InstanceDec
generateTupledInstance n = do
    cNames <- replicateM n (newName "c")

    let instOverlap :: Maybe Overlap
        instOverlap
          | n == 0    = Nothing
          | otherwise = Just Overlapping

        instCxt :: CxtQ
        instCxt = cxt (map varT cNames)

        instType :: TypeQ
        instType = foldr (\h -> appT (appT promotedConsT h)) promotedNilT (map varT cNames)

    iTyName <- newName "i"
    let iTy = varT iTyName

    iName <- newName "i"
    rName <- newName "r"

    let instAtPats :: [PatQ]
        instAtPats =
            [ [p| (SNat $(varP iName) :: SNat $iTy) |]
            , if n == 0 then wildP else varP rName
            ]

        ithCase :: Int -> MatchQ
        ithCase i
          | i < n =
              match (litP (IntegerL (fromIntegral i)))
                  (normalB [e|
                      case unsafeCoerce (Refl @($iTy)) :: $(peanoLit i) :~: $iTy of
                        Refl -> $(varE rName)
                  |])
                  []

          | i == n =
              match wildP
                  (normalB [e|
                      error $ "instAt @" ++ $(lift . pprint =<< instType) ++ " called with i = " ++ $(lift (show i))
                  |])
                  []

          | otherwise = error "impossible"

        instAtBody :: BodyQ
        instAtBody = normalB $ caseE (varE iName) (map ithCase [0..n])

        instAtImpl :: DecQ
        instAtImpl = funD 'instAt [clause instAtPats instAtBody []]

        instAtInline :: DecQ
        instAtInline = pragInlD 'instAt Inline FunLike AllPhases

    instanceWithOverlapD instOverlap instCxt [t| Tupled $instType |]
        [instAtImpl, instAtInline]

generateTupledInstancesFromTo :: Int -> Int -> Q [InstanceDec]
generateTupledInstancesFromTo k n =
    mapM generateTupledInstance [k..n]
