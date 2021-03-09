{-# language AllowAmbiguousTypes #-}
{-# language RoleAnnotations #-}
{-# language StrictData #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.HSmallArray
  ( HSmallArray
  , unsafeHSmallArrayFromListN
  , hSmallArrayToList
  ) where

import GHC.Exts (Any)

import Control.Lens qualified as L
import Control.Applicative (liftA2)
import Control.Monad.ST (ST)

import Data.Foldable (toList)

import qualified Data.Primitive.SmallArray as SA

import Unsafe.Coerce (unsafeCoerce)

import Data.Heterogeneous.Class.HCreate
import Data.Heterogeneous.Class.HDistributive
import Data.Heterogeneous.Class.HFoldable
import Data.Heterogeneous.Class.HFunctor
import Data.Heterogeneous.Class.HMonoid
import Data.Heterogeneous.Class.HTraversable
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.Class.Subseq
import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.TypeLevel.Subseq


-- SmallArray-based record type

type role HSmallArray representational nominal

type HSmallArray :: forall k. HTyConK k

newtype HSmallArray f as = HSmallArray (SA.SmallArray Any)


unsafeHSmallArrayFromListN :: SNat (Length as) -> [Any] -> HSmallArray f as
unsafeHSmallArrayFromListN n as = HSmallArray $ SA.smallArrayFromListN (snat n) as

hSmallArrayToList :: HSmallArray f as -> [Any]
hSmallArrayToList (HSmallArray arr) = toList arr


create :: forall as f.
    SNat (Length as)
    -> (forall i. i < Length as => SNat i -> f (as !! i))
    -> HSmallArray f as
create n f = HSmallArray $ SA.runSmallArray do
    marr :: SA.SmallMutableArray s Any
        <- SA.newSmallArray (snat n) (error "create: uninitialized element")

    let write :: i < Length as => SNat i -> ST s ()
        write i = SA.writeSmallArray marr (snat i) (unsafeCoerce $! f i)

    foldrNatInts n (\i st -> write i >> st) (return ())

    return marr


createST :: forall as f s.
    SNat (Length as)
    -> (forall i. i < Length as => SNat i -> ST s (f (as !! i)))
    -> ST s (HSmallArray f as)
createST n f = do
    mutArr <- SA.newSmallArray (snat n) (error "createST: uninitialized element")

    foldrNatInts n (\i st -> do
          !fa <- f i
          SA.writeSmallArray mutArr (snat i) (unsafeCoerce fa)
          st)
        (return ())

    arr <- SA.unsafeFreezeSmallArray mutArr
    return (HSmallArray arr)


newtype NewSArr a = NewSArr (forall s. ST s (SA.SmallMutableArray s a))

runNewSArr :: NewSArr a -> SA.SmallArray a
runNewSArr (NewSArr m) = SA.runSmallArray m


createA :: forall as f g.
    Applicative g
    => SNat (Length as)
    -> (forall i. i < Length as => SNat i -> g (f (as !! i)))
    -> g (HSmallArray f as)
createA n f =
    let newA :: NewSArr Any
        newA = NewSArr $
            SA.newSmallArray (snat n) (error "createA: uninitialized element")

        write :: forall i a. SNat i -> f a -> NewSArr Any -> NewSArr Any
        write i !fa (NewSArr marr) = NewSArr do
            arr <- marr
            arr <$ SA.writeSmallArray arr (snat i) (unsafeCoerce fa)
    in
        HSmallArray . runNewSArr <$> foldrNatInts n (\i -> liftA2 (write i) (f i)) (pure newA)
{-# inlinable [0] createA #-}
{-# rules "createA/createST" createA = createST #-}


unsafeIndex :: HSmallArray f as -> SNat i -> f (as !! i)
unsafeIndex (HSmallArray arr) i = unsafeCoerce $ SA.indexSmallArray arr (snat i)


index :: i < Length as => HSmallArray f as -> SNat i -> f (as !! i)
index = unsafeIndex


setIndex :: i < Length as => HSmallArray f as -> SNat i -> f (as !! i) -> HSmallArray f as
setIndex (HSmallArray arr) i !fa =
    HSmallArray $ SA.runSmallArray do
        marr <- SA.thawSmallArray arr 0 (SA.sizeofSmallArray arr)
        SA.writeSmallArray marr (snat i) (unsafeCoerce fa)
        return marr


unsafeSetIndex :: HSmallArray f as -> SNat i -> f a -> HSmallArray f bs
unsafeSetIndex (HSmallArray arr) i !fa = do
    HSmallArray $ SA.runSmallArray do
        marr <- SA.thawSmallArray arr 0 (SA.sizeofSmallArray arr)
        SA.writeSmallArray marr (snat i) (unsafeCoerce fa)
        return marr


size :: HSmallArray f as -> SNat (Length as)
size (HSmallArray arr) = SNat (SA.sizeofSmallArray arr)


_get :: forall a as f. KnownPeano (IndexOf a as) => HSmallArray f as -> f a
_get harrf =
    unsafeCoerce $ unsafeIndex harrf (getSNat @(IndexOf a as))


_set :: forall a b as bs f. KnownPeano (IndexOf a as) => HSmallArray f as -> f b -> HSmallArray f bs
_set (HSmallArray arr) !fb =
    HSmallArray $ SA.runSmallArray do
        marr <- SA.thawSmallArray arr 0 (SA.sizeofSmallArray arr)
        SA.writeSmallArray marr (peanoInt @(IndexOf a as)) (unsafeCoerce fb)
        return marr


unsafeIndexAll :: forall is ss rs f.
    ( KnownPeanos is
    , KnownLength ss
    )
    => HSmallArray f rs
    -> HSmallArray f ss
unsafeIndexAll (HSmallArray arr) =
    HSmallArray $
        SA.smallArrayFromListN (peanoInt @(Length ss)) $
            foldr (\ !x xs -> x : xs) [] $
                map (SA.indexSmallArray arr) (peanoInts @is)


getSubseq :: forall ss rs f.
    ( IsSubseqWithError ss rs
    , KnownPeanos (IndexesOfSubseq ss rs)
    , KnownLength ss
    )
    => HSmallArray f rs
    -> HSmallArray f ss
getSubseq = unsafeIndexAll @(IndexesOfSubseq ss rs)


_getSubset :: forall ss rs f.
    ( IsSubsetWithError ss rs
    , KnownPeanos (IndexesOf ss rs)
    , KnownLength ss
    )
    => HSmallArray f rs
    -> HSmallArray f ss
_getSubset = unsafeIndexAll @(IndexesOf ss rs)


_setSubset :: forall ss rs f.
    ( KnownPeanos (IndexesOf ss rs)
    , KnownLength ss
    )
    => HSmallArray f rs
    -> HSmallArray f ss
    -> HSmallArray f rs
_setSubset (HSmallArray arr) (HSmallArray upd) =
    HSmallArray $ SA.runSmallArray do
        marr <- SA.thawSmallArray arr 0 (SA.sizeofSmallArray arr)

        let go []       !_i = return ()
            go (ix:ixs) !i  = do
                SA.writeSmallArray marr ix $! SA.indexSmallArray upd i
                go ixs (i+1)

        go (peanoInts @(IndexesOf ss rs)) 0
        return marr


instance
    ( KnownPeano i
    , (as !! i) ~ a
    )
    => HGetI HSmallArray a as i where

    hgetC harrf = unsafeIndex harrf (getSNat @i)


instance
    ( KnownPeano i
    , HGetI HSmallArray a as i
    , HGetI HSmallArray b bs i
    , ReplaceSubseq '[a] '[b] as bs '[i]
    )
    => HSetI HSmallArray a b as bs i where

    hsetC fa harrf = unsafeSetIndex harrf (getSNat @i) fa


instance HIxed HSmallArray where
    hix i = L.lens (`index` i) (`setIndex` i)
    {-# inline hix #-}


instance HSingleton HSmallArray where
    hsingleton = L.iso (\(HSmallArray afas) -> unsafeCoerce (SA.indexSmallArray afas 0))
                       (\fa -> HSmallArray (SA.smallArrayFromListN 1 [unsafeCoerce fa]))
    {-# inline hsingleton #-}


instance HMonoid HSmallArray where
    hempty = HSmallArray mempty
    {-# inline hempty #-}

    happend (HSmallArray as) (HSmallArray bs) = HSmallArray (as <> bs)
    {-# inline happend #-}


instance KnownLength as => HCreate HSmallArray as where
    hcreateA = createA getSNat
    {-# inline hcreateA #-}


instance HFunctor HSmallArray where
    himap h harrf =
        create (size harrf) \i -> h i (index harrf i)
    {-# inline himap #-}

    hizipWith h harrf harrg =
        create (size harrf) \i -> h i (index harrf i) (index harrg i)
    {-# inline hizipWith #-}


instance HFoldable HSmallArray where
    hifoldr f z harr =
        foldrNatInts (size harr) (\i r -> f i (index harr i) r) z
    {-# inline hifoldr #-}

    hifoldr2 f z harrf harrg =
        foldrNatInts (size harrf) (\i r -> f i (index harrf i) (index harrg i) r) z
    {-# inline hifoldr2 #-}


instance HTraversable HSmallArray where
    htraverse h harrf =
        createA (size harrf) \i -> h (index harrf i)
    {-# inline htraverse #-}

    htraverse2 h harrf harrg =
        createA (size harrf) \i -> h (index harrf i) (index harrg i)
    {-# inline htraverse2 #-}


instance KnownLength as => HDistributive HSmallArray as



instance
    ( ReplaceSubseqWithError ss ss' rs rs'
    , is ~ IndexesOfSubseq ss rs
    , KnownLength ss
    , KnownLength rs'
    , KnownPeanos is
    )
    => HSubseqI HSmallArray ss ss' rs rs' is where

    hsubseqC = L.lens getSubseq \(HSmallArray ars) (HSmallArray ass') ->
        let
          replace :: Int -> [Int] -> [Any] -> [Any] -> [Any]
          replace !_ _  rs []  = rs
          replace !_ _  [] ss' = ss'
          replace !_ [] rs ss' = ss' ++ rs

          replace !i jjs@(j : js) (r : rs) s'ss'@(s' : ss')
            | i == j    = s' : replace (i+1) js rs ss'
            | otherwise = r : replace (i+1) jjs rs s'ss'

          ars' = SA.smallArrayFromListN (peanoInt @(Length rs')) $
              replace 0 (peanoInts @is) (toList ars) (toList ass')
        in
          HSmallArray ars'
    {-# inlinable hsubseqC #-}


instance
    ( ReplaceSubseqWithError ss '[] rs rs'
    , is ~ IndexesOfSubseq ss rs
    , KnownLength ss
    , KnownLength rs
    , KnownLength rs'
    , KnownPeanos is
    )
    => HQuotientI HSmallArray ss rs rs' is where

    hsubseqSplitC = L.iso
        (\(HSmallArray ars) ->
            let
              split :: Int -> [Any] -> [Int] -> ([Any], [Any])
              split !_ rs [] = ([], rs)

              split !i (r : rs) jjs@(j : js)
                | i == j    = case split (i+1) rs js  of (!ss, !rs') -> (r : ss, rs')
                | otherwise = case split (i+1) rs jjs of (!ss, !rs') -> (ss, r : rs')

              split !_ [] (_:_) = error "hsubseqSplitC @HSmallArray: split: the impossible happened"
            in
              case split 0 (toList ars) (peanoInts @is) of
                (ss, rs') -> (HSmallArray $ SA.smallArrayFromListN (peanoInt @(Length ss)) ss,
                              HSmallArray $ SA.smallArrayFromListN (peanoInt @(Length rs')) rs'))
        (\(HSmallArray ass, HSmallArray ars') ->
          let
            merge :: Int -> [Int] -> [Any] -> [Any] -> [Any]
            merge !_ [] [] rs' = rs'
            merge !_ _  ss []  = ss

            merge !i jjs@(j : js) sss@(s : ss) rrs'@(r : rs')
              | i == j    = s : merge (i+1) js ss rrs'
              | otherwise = r : merge (i+1) jjs sss rs'

            merge !_ [] (_:_) _ = error "hsubseqSplitC @HSmallArray: merge: the impossible happened"
            merge !_ (_:_) [] _ = error "hsubseqSplitC @HSmallArray: merge: the impossible happened"
          in
            HSmallArray $ SA.smallArrayFromListN (peanoInt @(Length rs)) $
                merge 0 (peanoInts @is) (toList ass) (toList ars'))
    {-# inlinable hsubseqSplitC #-}


