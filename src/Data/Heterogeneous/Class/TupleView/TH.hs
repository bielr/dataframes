{-# language ParallelListComp #-}
{-# language QuasiQuotes #-}
{-# language TemplateHaskell #-}
{-# language ViewPatterns #-}
module Data.Heterogeneous.Class.TupleView.TH where

import GHC.Tuple (Solo(..))

import Control.Monad
import Data.Foldable (foldl')

import Language.Haskell.TH
import Data.Heterogeneous.HTuple.HTuple (HTuple(..))


data GenHTupleCxt = GenHTupleCxt
    { gen_fTy       :: TypeQ   -- f
    , gen_aTys      :: [TypeQ] -- a1, a2  tyvars
    , gen_listTy    :: TypeQ   -- [a1, a2, ...] type

    , gen_aExps     :: [ExpQ]  -- fa1 fa2 vars
    , gen_aPats     :: [PatQ]  -- fa1 fa2 patterns

    , gen_tupTy     :: (TypeQ -> TypeQ) -> TypeQ -- (f a1, f a2..,) type
    , gen_tupPat    :: PatQ -- (fa1, fa2..,) pattern
    , gen_tupExp    :: (TypeQ -> ExpQ -> ExpQ) -> ExpQ -- ((a1, fa1) -> tuple element exp) -> tuple exp
    }


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

    let tupTy f
          | n == 0    = [t| () |]
          | n == 1    = foldl' appT [t|Solo|] (map f aTys)
          | otherwise = foldl' appT (tupleT n) (map f aTys)
        tupPat
          | n == 0    = [p| () |]
          | n == 1    = conP 'Solo (map bangP aPats)
          | otherwise = tupP (map bangP aPats)
        tupExp g
          | n == 0    = [e| () |]
          | n == 1    = foldl' appE [|Solo|] (zipWith g aTys aExps)
          | otherwise = tupE (zipWith g aTys aExps)


    return GenHTupleCxt
        { gen_fTy = fTy
        , gen_aTys = aTys
        , gen_listTy = listTy

        , gen_aPats = aPats
        , gen_aExps = aExps

        , gen_tupTy = tupTy
        , gen_tupPat = [p| HTuple $tupPat |]
        , gen_tupExp = \g -> [e| HTuple $(tupExp g) |]
        }


{-
generateHTupleInstance :: Int -> Q [Dec]
generateHTupleInstance n = do
    fTyName <- newName "f"
    let fTy = varT fTyName

    aTyNames <- replicateM n (newName "a")
    let aTys = map varT aTyNames

    aVarNames <- replicateM n (newName "a")
    let aPats = map varP aVarNames
        aExps = map varE aVarNames

    let listTy   = foldr (\a as -> [t| $a ': $as |]) [t| '[]  |] aTys
        recPat   = foldr (\a as -> [p| $a :& $as |]) [p| RNil |] aPats
        recExp g = foldr (\(aTy, aE) as -> [e| $(g aTy aE) :& $as |]) [e| RNil |] (zip aTys aExps)

    let arrCaseExp method arr body =
            [e|
                case toList $arr of
                    $anysPat -> $body
                    anys ->
                        error $ $(lift method) ++ " @" ++ $(lift . pprint =<< listTy)
                            ++ ": SARec of invalid size " ++ show (length anys)
                |]
          where
            anysPat = listP
                [ [p| (unsafeCoerce -> $(bangP aPat) :: $fTy $aTy) |]
                | aTy <- aTys
                | aPat <- aPats
                ]

        sarecExp g =
            [| SARec (fromListN $(lift n) $anysExp) |]
          where
            anysExp = listE
                [ [e| unsafeCoerce $(g aTy aExp) :: Any |]
                | aTy <- aTys
                | aExp <- aExps
                ]

    let tupTy f
          | n > 1     = foldl' appT (tupleT n) (map f aTys)
          | otherwise = foldl' appT (conT ''Solo) (map f aTys)
        tupPat
          | n > 1     = tupP (map bangP aPats)
          | otherwise = conP 'Solo (map bangP aPats)
        tupExp g
          | n > 1     = tupE (zipWith g aTys aExps)
          | otherwise = foldl' appE (conE 'Solo) (zipWith g aTys aExps)

    [d|
        type instance RTupleOf f $listTy = $(tupTy $ appT [t| f |])

        type instance RTupleHKDOf f $listTy = $(tupTy $ appT [t| HKD f |])

        instance RTupled Rec $listTy where
            rtupleWith     h $recPat = $(tupExp \_ -> appE [| h |])
            rtupleWithC    h $recPat = $(tupExp \_ -> appE [| h |])
            rtupleHKDWith  h $recPat = $(tupExp \_ -> appE [| toHKD . h |])
            rtupleHKDWithC h $recPat = $(tupExp \_ -> appE [| toHKD . h |])

            fromRTuple    $tupPat = $(recExp \_ -> id)
            fromRTupleHKD $tupPat = $(recExp \_ -> appE [| unHKD |])

        instance RTupled SARec $listTy where
            rtupleWith h (SARec arr :: SARec $fTy $listTy) =
                $(arrCaseExp "rtupleWith"     [| arr |] (tupExp \_ -> appE [| h |]))
            rtupleWithC h (SARec arr :: SARec $fTy $listTy) =
                $(arrCaseExp "rtupleWithC"    [| arr |] (tupExp \_ -> appE [| h |]))
            rtupleHKDWith h (SARec arr :: SARec $fTy $listTy) =
                $(arrCaseExp "rtupleHKDWith " [| arr |] (tupExp \_ -> appE [| toHKD . h |]))
            rtupleHKDWithC h (SARec arr :: SARec $fTy $listTy) =
                $(arrCaseExp "rtupleHKDWithC" [| arr |] (tupExp \_ -> appE [| toHKD . h |]))

            fromRTuple $tupPat = $(sarecExp \_ -> id)

            fromRTupleHKD :: forall f. (forall a. IsoHKD f a) => RTupleHKDOf f $listTy -> SARec f $listTy
            fromRTupleHKD $tupPat = $(sarecExp \aTy -> appE [| unHKD @f @($aTy) |])
      |]


generateHTupleInstancesFromTo :: Int -> Int -> Q [Dec]
generateHTupleInstancesFromTo k n =
    concat <$> mapM generateHTupleInstance [k..n]
    -}
