{-# options_ghc -ddump-splices -Wno-error=unused-do-bind #-}
{-# language QualifiedDo #-}
{-# language ImplicitParams #-}
{-# language OverloadedLabels #-}
{-# language TemplateHaskell #-}
module Main where

import Control.Lens

import Data.Frame.Class
import Data.Frame.Impl.ColVectors
import Data.Frame.Kind
import Data.Frame.Pipe qualified as Pipe
import Data.Frame.TH.Expr (rowwise)



-- test :: Env Frame '["a":>Int, "b":>Char, "c":>Double] Double
-- test = do
--     a <- col #a
--     c <- col #c
--     pure (fromIntegral a + c)


test2 :: Env Frame '["a":>Int, "b":>Char, "c":>Double] Double
test2 = $(rowwise [| fromIntegral ?a + ?c |])
--       [rowwise| fromIntegral #a + #c*#a |]


testAppend ::
    Frame '["a":>Int, "b":>Char, "c":>Double]
    -> _
testAppend = Pipe.do
    appendCol #d $(rowwise [| fromIntegral ?a + ?c |])

    appendCol #e $(rowwise [| show ?d |])

    restricting (#a,#c) %~ Pipes.do
        transmute (#c, #a) $(rowwise [| (?c+1, ?a-1) |])


main :: IO ()
main = undefined
