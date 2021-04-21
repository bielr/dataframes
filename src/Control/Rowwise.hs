{-# language MagicHash #-}
module Control.Rowwise
  ( Rowwise
  , runRowwise#
  , runRowwise
  , rowwise#
  , rowwise
  , withCtx
  , rowid
  ) where

import GHC.Exts


newtype Rowwise ctx a = Rowwise { runRowwise# :: ctx -> Int# -> a }


runRowwise :: Rowwise ctx a -> ctx -> Int -> a
runRowwise (Rowwise cixa) = \ !c ->
    let !ixa = cixa c
    in  \(I# i) -> ixa i


rowwise# :: (ctx -> Int# -> a) -> Rowwise ctx a
rowwise# cixa = Rowwise \c -> cixa $! c


rowwise :: (ctx -> Int -> a) -> Rowwise ctx a
rowwise cixa = Rowwise \ !c ->
    let !ixa = cixa c
    in  \i -> ixa (I# i)


instance Functor (Rowwise ctx) where
    fmap f (Rowwise cixa) = Rowwise \ !c ->
        let !ixa = cixa c
        in  \i -> f (ixa i)


instance Applicative (Rowwise ctx) where
    pure !a = Rowwise \ !_ -> \_ -> a

    Rowwise cixf <*> Rowwise cixa = Rowwise \ !c ->
        let !ixf = cixf c
            !ixa = cixa c
        in \i -> ixf i (ixa i)


withCtx :: (ctx -> a) -> Rowwise ctx a
withCtx f = Rowwise \ !ctx ->
    let !a = f ctx
    in  \_ -> a


rowid :: Rowwise ctx Int
rowid = Rowwise \ !_ ->
    \i -> I# i
