{-# options_ghc -Wno-error=unused-do-bind -fplugin=Data.Frame.Plugin #-}
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
import Data.Frame.Impl.ColVectors
import Data.Frame.Kind
import Data.Frame.Pipe qualified as Pipe
import Data.Frame.TH.Expr (env)
import Data.Frame.TypeIndex



-- test :: Env Frame '["a":>Int, "b":>Char, "c":>Double] Double
-- test = do
--     a <- col #a
--     c <- col #c
--     pure (fromIntegral a + c)


myDF :: Frame _
Just myDF = fromCols
    ( #a =.. [1, 2, 3, 4 :: Int]
    , #b =.. ["a", "b", "c", "d" :: Text]
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


main :: IO ()
main = undefined
