{-# language DeriveFunctor #-}
module Control.Rowwise
  ( Rowwise
  , runRowwise
  , unsafeRowwise
  , withCtx
  , rowid
  ) where

import Data.Profunctor.Unsafe


newtype Rowwise ctx a = Rowwise { runRowwise :: ctx -> Int -> a }
    deriving (Functor)


unsafeRowwise :: (ctx -> Int -> a) -> Rowwise ctx a
unsafeRowwise = Rowwise


instance Applicative (Rowwise ctx) where
    pure a = Rowwise \_ _ -> a

    Rowwise cixf <*> Rowwise cixa = Rowwise \c ->
        let !ixf = cixf c
            !ixa = cixa c
        in ixf <*> ixa


instance Profunctor Rowwise where
    dimap l r (Rowwise cixa) = Rowwise ((r .) . cixa . l)
    rmap r (Rowwise cixa) = Rowwise ((r .) . cixa)
    lmap l (Rowwise cixa) = Rowwise (cixa . l)

    r #. Rowwise cixa = Rowwise ((r #.) #. cixa)
    Rowwise cixa .# l = Rowwise (cixa .# l)


withCtx :: (ctx -> a) -> Rowwise ctx a
withCtx f = Rowwise \ctx ->
    let !a = f ctx
    in const a


rowid :: Rowwise ctx Int
rowid = Rowwise \_ -> id


-- colIx :: When (rep == 'Vec) (ColType col) => Col rep col -> Int -> Snd col
-- colIx = \case
--     ColVec v             -> coerce (v VG.!)
--     ColGen (Indexer _ a) -> coerce a

--
-- runColIx :: forall col' s a rep by rec cols.
--     ( When (rep == 'Vec) (ColType col')
--     , col' ~ '(s, a)
--     )
--     => Frame rep by rec cols -> Rowwise (Frame rep by rec cols) a -> Col rep '(s, a)
-- runColIx ctx (Rowwise dfixa) =
--     let !g = dfixa ctx
--     in
--         case ctx of
--           RowsVec _   -> generateCol $ Indexer (nrows ctx) g
--           RowsGen _   -> generateCol $ Indexer (nrows ctx) g
--           ColVecs _ _ -> generateCol $ Indexer (nrows ctx) g
--           ColGens _ _ -> generateCol $ Indexer (nrows ctx) g
