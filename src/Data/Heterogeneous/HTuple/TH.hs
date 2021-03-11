{-# language ParallelListComp #-}
{-# language TemplateHaskell #-}
module Data.Heterogeneous.HTuple.TH where

import GHC.Tuple
import Language.Haskell.TH
import Data.Foldable (foldl')
import Control.Monad (replicateM)

import Data.Heterogeneous.HTuple.HTuple
import Data.Heterogeneous.TypeLevel


data GenHTupleCxt = GenHTupleCxt
    { gen_fTy     :: TypeQ   -- f
    , gen_aTys    :: [TypeQ] -- a1, a2  tyvars
    , gen_listTy  :: TypeQ   -- [a1, a2, ...] type

    , gen_aExps   :: [ExpQ]  -- fa1 fa2 vars
    , gen_aPats   :: [PatQ]  -- fa1 fa2 patterns

    , gen_tupTy   :: (TypeQ -> TypeQ) -> TypeQ -- (f a1, f a2..,) type
    , gen_tupPat  :: PatQ -- (fa1, fa2..,) pattern
    , gen_tupExp  :: (Int -> TypeQ -> ExpQ -> ExpQ) -> ExpQ -- ((i, ai, fai) -> ith tuple element exp) -> tuple exp
    , gen_tupExp' :: (Int -> TypeQ -> ExpQ -> ExpQ) -> ExpQ -- ((i, ai, fai) -> ith tuple element exp) -> strict tuple exp
    }


peanoTys :: [TypeQ]
peanoTys = iterate (\i -> [t| 'Succ $i |]) [t| 'Zero |]


htupleInstanceContext :: Int -> Q GenHTupleCxt
htupleInstanceContext n = do
    fTyName <- newName "f"
    let fTy = varT fTyName

    aTyNames <- replicateM n (newName "a")
    let aTys = map varT aTyNames

    aVarNames <- replicateM n (newName "a")
    let aPats = map varP aVarNames
        aExps = map varE aVarNames

    let listTy   = foldr (\a as -> [t| $a ': $as |]) [t| '[]  |] aTys

    --  recPat   = foldr (\a as -> [p| $a :& $as |]) [p| RNil |] aPats
    --  recExp g = foldr (\(aTy, aE) as -> [e| $(g aTy aE) :& $as |]) [e| RNil |] (zip aTys aExps)

    let tupTy :: (TypeQ -> TypeQ) -> TypeQ
        tupTy f
          | n == 0    = [t| () |]
          | n == 1    = foldl' appT [t|Solo|] (map f aTys)
          | otherwise = foldl' appT (tupleT n) (map f aTys)

        tupPat :: PatQ
        tupPat
          | n == 0    = [p| HTuple () |]
          | n == 1    = [p| HTuple $(conP 'Solo (map bangP aPats)) |]
          | otherwise = [p| HTuple $(tupP (map bangP aPats)) |]

        tupExp :: (Int -> TypeQ -> ExpQ -> ExpQ) -> ExpQ
        tupExp g
          | n == 0    = [e| HTuple () |]
          | n == 1    = [e| HTuple $(foldl' appE [|Solo|] (zipWith3 g [0..] aTys aExps)) |]
          | otherwise = [e| HTuple $(tupE (zipWith3 g [0..] aTys aExps)) |]

        tupExp' :: (Int -> TypeQ -> ExpQ -> ExpQ) -> ExpQ
        tupExp' g     = do
            aVarNames' <- replicateM n (newName "a'")
            let aPats' = map (bangP.varP) aVarNames'
                aExps' = map varE aVarNames'

            letE
                [ valD aPat' (normalB (g i aTy aExp)) []
                | i <- [0..]
                | aPat' <- aPats'
                | aTy <- aTys
                | aExp <- aExps
                ]
                [e| HTuple $(tupE aExps') |]


    return GenHTupleCxt
        { gen_fTy = fTy
        , gen_aTys = aTys
        , gen_listTy = listTy

        , gen_aPats = aPats
        , gen_aExps = aExps

        , gen_tupTy = tupTy
        , gen_tupPat = tupPat
        , gen_tupExp = tupExp
        , gen_tupExp' = tupExp'
        }
