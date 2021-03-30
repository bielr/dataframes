{-# options_ghc -Wno-error=unused-do-bind #-}
{-# language QualifiedDo #-}
{-# language ImplicitParams #-}
{-# language OverloadedLabels #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language TemplateHaskell #-}
{-# language TupleSections #-}
module Main where

import Control.Lens
import GHC.Tuple
import Data.Text (Text)

import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.HTuple
import Data.Frame.Class
import Data.Frame.DataTypes.Vector qualified as DT
import Data.Frame.Impl.ColVectors
import Data.Frame.Kind
import Data.Frame.Pipe qualified as Pipe
import Data.Frame.TH.Expr (rowwise)
import Data.Frame.TypeIndex



type instance DT.VectorModeOf Text = 'DT.Boxed


-- test :: Env Frame '["a":>Int, "b":>Char, "c":>Double] Double
-- test = do
--     a <- col #a
--     c <- col #c
--     pure (fromIntegral a + c)


myDF :: Frame '["a":>Int, "b":>Text]
myDF = fromCols
    ( #a =.. [1, 2, 3, 4]
    , #b =.. ["a", "b", "c", "d"]
    )


test2 :: Env Frame '["a":>Int, "b":>Char, "c":>Double] Double
test2 = $(rowwise [| fromIntegral ?a + ?c |])
--       [rowwise| fromIntegral #a + #c*#a |]


testAppend ::
    Frame '["a":>Int, "b":>Char, "c":>Double]
    -> _
testAppend = Pipe.do
    appendCol #d $(rowwise [| fromIntegral ?a + ?c |])

    appendCol #e $(rowwise [| show ?d |])

    restricting (#a,#c) %~ Pipe.do
        transmute (#x,#y) $(rowwise [| (?c+1, ?a-1) |])


main :: IO ()
main = undefined
