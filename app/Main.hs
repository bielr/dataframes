{-# options_ghc -Wno-error=unused-do-bind -fplugin=Data.Frame.Plugin #-}
{-# language PartialTypeSignatures #-}
{-# language QualifiedDo #-}
{-# language ImplicitParams #-}
{-# language OverloadedLabels #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TemplateHaskell #-}
{-# language TupleSections #-}
module Main where

import Control.Lens
import GHC.Tuple
import Data.Text (Text)

import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.HTuple
import Data.Frame.Class
import Data.Frame.DataTypes.VectorMode
import Data.Frame.Display
import Data.Frame.Impl.ColVectors
import Data.Frame.Kind
import Data.Frame.Pipe qualified as Pipe
import Data.Frame.TH.Eval
import Data.Frame.TypeIndex



-- test :: Env Frame '["a":>Int, "b":>Char, "c":>Double] Double
-- test = do
--     a <- col #a
--     c <- col #c
--     pure (fromIntegral a + c)

data EvilShow = EvilShow
type instance VectorModeOf EvilShow = 'Boxed

instance Show EvilShow where
    show EvilShow = "oo\t\rps\nas\0df"


myDF :: Frame _
Just myDF = fromCols_
    ( #a =.. [1, 2, 3, 44444444 :: Int]
    , #b =.. ["a", "b", "c", "ddddddddddddddddddddddddddddddd" :: Text]
    , #c =.. [[0], [0..1], [0..2], [0..3] :: [Int]]
    , #d =.. [EvilShow, EvilShow, EvilShow, EvilShow]
    )


test2 :: Env Frame '["a":>Int, "b":>Char, "c":>Double] Double
test2 = [_row| fromIntegral ?a + ?c |]


testAppend ::
    Frame '["a":>Int, "b":>Char, "c":>Double]
    -> _
testAppend = Pipe.do
    appendCol [_row| #d =. fromIntegral ?a + ?c |]

    appendCol [_row| #e =. show ?d |]

    restricting (#a, #c) %~ Pipe.do
        transmute [_row| (#x =. ?c+1 , #y =. ?a-1) |]


testPrint :: IO ()
testPrint = do
    let Just df = fromCols_ @Frame (Solo (#b =.. [0..10 :: Int]))

    printFrameWith defaultShowOptions { cellMaxWidth = 50 } $ df & Pipe.do
        appendCol $(env [| #c =. show ?b |])

        transmute $(env [|
            let x = ?b + read ?c
            in (#x =. x, #sqrt_x =. sqrt (fromIntegral x :: Float))
          |])

        appendCol $(env [| #sqrt_x_sq =. ?sqrt_x**2 |])

        appendCol $(env [| #diff =. fromIntegral ?x - ?sqrt_x_sq |])


testPrintWithPlugin :: IO ()
testPrintWithPlugin = do
    let Just df = fromCols_ @Frame (Solo (#b =.. [0..10 :: Int]))

    printFrameWith defaultShowOptions { cellMaxWidth = 50 } $ df & Pipe.do
        appendCol [_row| #c =. show ?b |]

        transmute [_row|
            let x = ?b + read ?c
            in (#x =. x, #sqrt_x =. sqrt (fromIntegral x :: Float))
          |]

        appendCol [_row| #sqrt_x_sq =. ?sqrt_x**2 |]

        appendCol [_row| #diff =. fromIntegral ?x - ?sqrt_x_sq |]


main :: IO ()
main = testPrintWithPlugin -- printFrame myDF
