{-# options_ghc -Wno-error=unused-do-bind -fplugin=Data.Frame.Plugin
    -O2 -ddump-to-file -ddump-simpl -dsuppress-idinfo -dsuppress-unfoldings -dsuppress-coercions #-}
--  #-}
{-# language ImplicitParams #-}
{-# language OverloadedLabels #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language PartialTypeSignatures #-}
{-# language QualifiedDo #-}
{-# language QuasiQuotes #-}
{-# language TemplateHaskell #-}
{-# language TupleSections #-}
module Main where

import Control.Lens
import GHC.Tuple
import Data.Text (Text)
import Text.Read (readMaybe)

import Data.Frame.DataTypes.VectorMode
import Data.Frame.Display
import Data.Frame.Kind
import Data.Frame.Pipe qualified as Pipe
import Data.Frame.Sugar
import Data.Frame.TH.Eval



-- test :: Env Frame '["a":>Int, "b":>Char, "c":>Double] Double
-- test = do
--     a <- col #a
--     c <- col #c
--     pure (fromIntegral a + c)


data EvilShow = EvilShow
type instance VectorModeOf EvilShow = 'Boxed

instance Show EvilShow where
    show EvilShow = "oo\t\rps\nas\0df"


testFromCols :: Frame _
testFromCols = frameFromCols
    ( #a =.. [1, 2, 3, 44444444 :: Int]
    , #b =.. ["a", "b", "c", "ddddddddddddddddddddddddddddddd" :: Text]
    , #c =.. [[0], [0..1], [0..2], [0..3] :: [Int]]
    , #d =.. [EvilShow, undefined, EvilShow, EvilShow]
    )
{-# noinline testFromCols #-}


testEval :: Eval Frame '["a":>Int, "b":>Char, "c":>Double] (Field ("d":>Double))
testEval = [_eval| #d =. fromIntegral ?a + ?c |]


testAppend ::
    Frame '["a":>Int, "b":>Char, "c":>Double]
    -> Frame _
testAppend = Pipe.do
    appendCol [_eval| #d =. fromIntegral ?a + ?c |]

    appendCol [_eval| #e =. (? fmap show (val #d)) |]

    -- restricting (#a, #c) %~ Pipe.do
    --     transmute [_eval| (#x =. ?c+1 , #y =. ?a-1) |]


testInference :: IO ()
testInference =
    frameFromCols (Solo (#b =.. [0..10 :: Int]))
        & appendCol $(eval [| #c =. show ?b |])

        & transmute' $(eval [|
            let x = ?b + read ?c
            in (#x =. x, #sqrt_x =. sqrt (fromIntegral x :: Float))
          |])

        & appendCol $(eval [| #sqrt_x_sq =. ?sqrt_x**2 |])

        & appendCol $(eval [| #diff =. fromIntegral ?x - ?sqrt_x_sq |])

        & printFrameWith defaultShowOptions { cellMaxWidth = 50 }
{-# noinline testInference #-}


testSingleTransmute :: Frame '["b":>Int] -> IO ()
testSingleTransmute df = df
    & transmute' [_eval|
        let c = show ?b
            x = ?b + read c
            sqrt_x = sqrt (fromIntegral x :: Float)
            sqrt_x_sq = sqrt_x**2
            diff = fromIntegral x - sqrt_x_sq
        in
            (#c =. c, #x =. x, #sqrt_x =. sqrt_x, #sqrt_x_sq =. sqrt_x_sq, #diff =. diff)
        |]

    & printFrameWith defaultShowOptions { cellMaxWidth = 50 }
{-# noinline testSingleTransmute #-}


testTransmuteAppend :: Frame '["b":>Int] -> IO ()
testTransmuteAppend df = df
    & appendCol [_eval| #str_b =. show ?b |]

    & appendColsMaybe [_eval| do
        cInt <- readMaybe (? val #str_b)
        let x = ?b + cInt

        if x < -5 then
            Nothing
        else
            Just (#x =. x, #sqrt_x =. sqrt (fromIntegral x :: Float))
        |]

    & appendCol [_eval| #sqrt_x_sq =. ?sqrt_x**2 |]
    & appendCol [_eval| #diff =. fromIntegral ?x - ?sqrt_x_sq |]

    & printFrame
{-# noinline testTransmuteAppend #-}


main :: IO ()
main = testTransmuteAppend $
    generateFrame @Frame @'[_] $ Indexer 20 \i ->
        HTuple (Solo (#b =. i - 10))
