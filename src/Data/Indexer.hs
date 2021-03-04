{-# language DeriveFunctor #-}
{-# language StrictData #-}
module Data.Indexer where

import Control.Lens.Indexed (FunctorWithIndex(..), FoldableWithIndex(..))
import qualified Control.Lens as L

import Data.Functor ((<&>))
import Data.Foldable (Foldable(..))
import Data.Semigroup (Semigroup(..))

import qualified Data.Vector         as VB
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU


data Indexer a = Indexer {-# unpack #-} Int (Int -> a)
    deriving Functor


elemAt :: Indexer a -> Int -> a
elemAt (Indexer _ ia) = ia
{-# inline elemAt #-}


indexVector :: VG.Vector v a => v a -> Indexer a
indexVector v = Indexer (VG.length v) (v VG.!)
{-# inline indexVector #-}


copyIndexer :: VG.Vector v a => Indexer a -> v a
copyIndexer (Indexer n ia) = VG.generate n ia
{-# inline copyIndexer #-}


asIndexer :: (VG.Vector v a, VG.Vector w b) => L.Iso (v a) (w b) (Indexer a) (Indexer b)
asIndexer = L.iso indexVector copyIndexer
{-# inline asIndexer #-}


backpermuteIndexer :: Indexer a -> Indexer Int -> Indexer a
backpermuteIndexer (Indexer _ ixa) (Indexer n ixi) = Indexer n (ixa . ixi)
{-# inline backpermuteIndexer #-}


concatIndexersN :: forall a. Int -> [Indexer a] -> Indexer a
concatIndexersN m ixs = Indexer n ia
  where
    vixs :: VB.Vector (Indexer a)
    vixs = VB.fromListN m ixs

    breaks :: VU.Vector Int
    breaks = VU.postscanl' (+) 0 $ VU.convert $ VB.map length $ vixs

    n :: Int
    n = VU.last breaks

    ia :: Int -> a
    ia i =
        case VU.findIndex (i <) breaks of
          Just j  ->
              let Indexer nj iaj = VB.unsafeIndex vixs j
                  !i'            = i - (VU.unsafeIndex breaks j - nj)
              in  iaj i'
          Nothing ->
              error $ "concatIndexersN: index " ++ show i ++ " out of bounds: " ++ show n



instance Applicative Indexer where
    pure a = Indexer maxBound (const a)
    {-# inline pure #-}
    ff <*> fa = Indexer (min (length ff) (length fa)) (elemAt ff <*> elemAt fa)
    {-# inline (<*>) #-}


instance Semigroup (Indexer a) where
    Indexer n ia <> Indexer m ib = Indexer (n+m) ic
      where
        ic i
            | i < n     = ia i
            | otherwise = ib (i-n)
    {-# inline (<>) #-}

    sconcat = mconcat . toList
    {-# inline sconcat #-}


instance Monoid (Indexer a) where
    mempty = Indexer 0 (const (error "empty Indexer"))
    {-# inline mempty #-}

    mconcat ixs = concatIndexersN (length ixs) ixs
    {-# inline mconcat #-}


instance Foldable Indexer where
    foldl' f !z (Indexer n ia) = go z 0
      where
        go !acc !i
          | i <  n    = go (f acc (ia i)) (i+1)
          | otherwise = acc
    {-# inline foldl' #-}

    foldr f z ix = foldr f z (toList ix)
    {-# inline foldr #-}

    toList (Indexer n ia) = map ia [0..n-1]
    {-# inline toList #-}

    length (Indexer n _) = n
    {-# inline length #-}


instance FunctorWithIndex Int Indexer where
    imap f (Indexer n ia) = Indexer n (\i -> f i (ia i))
    {-# inline imap #-}


instance FoldableWithIndex Int Indexer where
    ifoldMap f ix = ifoldr (\i a acc -> f i a <> acc) mempty ix
    {-# inline ifoldMap #-}

    ifoldr f z (Indexer n ia) = go z 0
      where
        go acc !i
          | i < n     = f i (ia i) (go acc (i+1))
          | otherwise = acc
    {-# inline ifoldr #-}

    ifoldl' f z (Indexer n ia) = go z 0
      where
        go !acc !i
          | i <  n    = let acc' = f i acc (ia i) in go acc' (i+1)
          | otherwise = acc
    {-# inline ifoldl' #-}


type instance L.Index (Indexer a) = Int
type instance L.IxValue (Indexer a) = a

instance L.Ixed (Indexer a) where
    ix i f ix@(Indexer n a)
      | 0 <= i && i < n = f (a i) <&> \b -> Indexer n (\j -> if i == j then b else a i)
      | otherwise       = pure ix
    {-# inline ix #-}
