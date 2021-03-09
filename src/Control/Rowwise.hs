{-# language DeriveFunctor #-}
module Control.Rowwise
  ( Rowwise
  , global
  ) where

import Data.Profunctor.Unsafe


newtype Rowwise ctx a = Rowwise (ctx -> Int -> a)
    deriving (Functor)


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


global :: (df -> a) -> Rowwise df a
global f = Rowwise \df ->
    let !a = f df
    in const a


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
-- runColIx df (Rowwise dfixa) =
--     let !g = dfixa df
--     in
--         case df of
--           RowsVec _   -> generateCol $ Indexer (nrows df) g
--           RowsGen _   -> generateCol $ Indexer (nrows df) g
--           ColVecs _ _ -> generateCol $ Indexer (nrows df) g
--           ColGens _ _ -> generateCol $ Indexer (nrows df) g
