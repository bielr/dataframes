{-# language AllowAmbiguousTypes #-}
{-# language RoleAnnotations #-}
{-# language UndecidableInstances #-}
{-# language TemplateHaskell #-}
module Data.Heterogeneous.HSmallArray
  ( HSmallArray
  , unsafeHSmallArrayFromListN
  , hSmallArrayToList
  ) where

import GHC.Exts (Any)
import Control.Applicative (liftA2)
import Control.Lens qualified as L
import Control.Monad.ST (ST)
import Data.Foldable (toList)
import Data.Hashable (Hashable(..))
import Data.Primitive.SmallArray qualified as SA
import Data.Traversable (forM)
import Language.Haskell.TH qualified as TH
import Text.Show (showListWith)

import Unsafe.Coerce (unsafeCoerce)

import Data.Heterogeneous.Constraints
import Data.Heterogeneous.Class.HApply
import Data.Heterogeneous.Class.HConv
import Data.Heterogeneous.Class.HCreate
import Data.Heterogeneous.Class.HDistributive
import Data.Heterogeneous.Class.HFoldable
import Data.Heterogeneous.Class.HFunctor
import Data.Heterogeneous.Class.HMonoid
import Data.Heterogeneous.Class.HTraversable
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.Class.Subseq
import Data.Heterogeneous.Class.Subset
import Data.Heterogeneous.Class.TupleView
import Data.Heterogeneous.HList qualified as HList
import Data.Heterogeneous.HTuple.TH
import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.TypeLevel.Subseq


-- SmallArray-based record type

type role HSmallArray representational nominal

type HSmallArray :: forall k. HTyConK k

newtype HSmallArray f as = HSmallArray (SA.SmallArray Any)


hSmallArrayToList :: HSmallArray f as -> [Any]
hSmallArrayToList (HSmallArray arr) = toList arr


uninitializedElement :: String -> Any
uninitializedElement origin =
    error ("Data.Heterogeneous.HSmallArray: " ++ origin ++ ": uninitialized element")


unsafeHSmallArrayFromListN :: SNat (Length as) -> [Any] -> HSmallArray f as
unsafeHSmallArrayFromListN n as = HSmallArray $ SA.runSmallArray do
    marr :: SA.SmallMutableArray s Any
        <- SA.newSmallArray (snat n) (uninitializedElement "unsafeHSmallArrayFromListN")

    let go :: Int -> [Any] -> ST s ()
        go !_ []     = return ()
        go !i (b:bs) = SA.writeSmallArray marr i (unsafeCoerce $! b) >> go (i+1) bs

    go 0 as

    return marr


create :: forall as f.
    SNat (Length as)
    -> (forall i. i < Length as => SNat i -> f (as !! i))
    -> HSmallArray f as
create n f = HSmallArray $ SA.runSmallArray do
    marr :: SA.SmallMutableArray s Any
        <- SA.newSmallArray (snat n) (uninitializedElement "create")

    let write :: i < Length as => SNat i -> ST s ()
        write i = SA.writeSmallArray marr (snat i) (unsafeCoerce $! f i)

    foldrNatInts n (\i st -> write i >> st) (return ())

    return marr


createST :: forall as f s.
    SNat (Length as)
    -> (forall i. i < Length as => SNat i -> ST s (f (as !! i)))
    -> ST s (HSmallArray f as)
createST n f = do
    mutArr <- SA.newSmallArray (snat n) (uninitializedElement "createST")

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
            SA.newSmallArray (snat n) (uninitializedElement "createA")

        write :: forall i a. SNat i -> f a -> NewSArr Any -> NewSArr Any
        write i !fa (NewSArr marr) = NewSArr do
            arr <- marr
            arr <$ SA.writeSmallArray arr (snat i) (unsafeCoerce fa)
    in
        HSmallArray . runNewSArr <$> foldrNatInts n (\i -> liftA2 (write i) (f i)) (pure newA)
{-# inlinable [0] createA #-}
{-# rules "createA/createST" createA = createST #-}


unsafeIndex :: HSmallArray f as -> SNat i -> f a
unsafeIndex (HSmallArray arr) i = unsafeCoerce $ SA.indexSmallArray arr (snat i)
{-# noinline unsafeIndex #-}


index :: i < Length as => HSmallArray f as -> SNat i -> f (as !! i)
index = unsafeIndex


indexViaSubseq :: IsSubseqI '[a] as '[i] => HSmallArray f as -> SNat i -> f a
indexViaSubseq = unsafeIndex


unsafeSetIndex :: HSmallArray f as -> SNat i -> f a -> HSmallArray f bs
unsafeSetIndex (HSmallArray arr) i !fa = do
    HSmallArray $ SA.runSmallArray do
        marr <- SA.thawSmallArray arr 0 (SA.sizeofSmallArray arr)
        SA.writeSmallArray marr (snat i) (unsafeCoerce fa)
        return marr
{-# noinline unsafeSetIndex #-}


setIndex :: i < Length as => HSmallArray f as -> SNat i -> f (as !! i) -> HSmallArray f as
setIndex = unsafeSetIndex


setIndexViaSubseq ::
    ReplaceSubseqI '[a] '[b] as bs '[i]
    => HSmallArray f as
    -> SNat i
    -> f b
    -> HSmallArray f bs
setIndexViaSubseq = unsafeSetIndex


size :: HSmallArray f as -> SNat (Length as)
size (HSmallArray arr) = SNat (SA.sizeofSmallArray arr)


unsafeIndexAll :: forall is ss rs f.
    ( KnownPeanos is
    , KnownLength ss
    )
    => HSmallArray f rs
    -> HSmallArray f ss
unsafeIndexAll (HSmallArray arr) =
    HSmallArray $ SA.runSmallArray do
        marr <- SA.newSmallArray (peanoInt @(Length ss)) (uninitializedElement "unsafeIndexAll")

        L.iforM_ (peanoInts @is) \i j ->
            SA.writeSmallArray marr i $! SA.indexSmallArray arr j

        return marr


getSubseq :: forall is ss rs f.
    ( IsSubseqI ss rs is
    , KnownPeanos is
    , KnownLength ss
    )
    => HSmallArray f rs
    -> HSmallArray f ss
getSubseq = unsafeIndexAll @is
{-# inline getSubseq #-}


getSubset :: forall is ss rs f.
    ( IndexAll rs is ~ ss
    , KnownPeanos is
    , KnownLength ss
    )
    => HSmallArray f rs
    -> HSmallArray f ss
getSubset = unsafeIndexAll @is
{-# inline getSubset #-}


setSubset :: forall is ss rs f.
    ( IndexAll rs is ~ ss
    , KnownPeanos is
    , KnownLength ss
    )
    => HSmallArray f ss
    -> HSmallArray f rs
    -> HSmallArray f rs
setSubset (HSmallArray upd) (HSmallArray arr) =
    HSmallArray $ SA.runSmallArray do
        marr <- SA.thawSmallArray arr 0 (SA.sizeofSmallArray arr)

        L.iforM_ (peanoInts @is) \j i ->
            SA.writeSmallArray marr i $! SA.indexSmallArray upd j

        return marr
{-# inlinable setSubset #-}


instance AllF Eq f as => Eq (HSmallArray f as) where
    (==) =
        hifoldr2 (\i a b eq -> constrained @(ComposeC Eq f) @as (a == b) i && eq) True
    {-# inline (==) #-}


instance (AllF Eq f as, AllF Ord f as) => Ord (HSmallArray f as) where
    compare =
        hifoldr2 (\i a b eq -> constrained @(ComposeC Ord f) @as (compare a b) i <> eq) EQ
    {-# inline compare #-}


instance AllF Show f as => Show (HSmallArray f as) where
    showsPrec _ =
        showListWith id
        . hitoListWith \i a -> constrained @(ComposeC Show f) @as (shows a) i
    {-# inlinable showsPrec #-}


instance AllF Hashable f as => Hashable (HSmallArray f as) where
    hash =
        hifoldl' (\h i a ->
            case snat i of
                0 -> constrained @(ComposeC Hashable f) @as (hash a) i
                _ -> constrained @(ComposeC Hashable f) @as (h `hashWithSalt` a) i)
            0
    {-# inline hash #-}

    hashWithSalt =
        hifoldl' \h i a ->
            case snat i of
                0 -> constrained @(ComposeC Hashable f) @as (hash a) i
                _ -> constrained @(ComposeC Hashable f) @as (h `hashWithSalt` a) i
    {-# inline hashWithSalt #-}


instance KnownPeano i => HGetI HSmallArray as i where
    hgetI harrf = unsafeIndex harrf (getSNat @i)
    {-# inline hgetI #-}


instance
    ( KnownPeano i
    , HGetI HSmallArray as i
    , a ~ as !! i
    , HGetI HSmallArray bs i
    , b ~ bs !! i
    , ReplaceSubseqI '[a] '[b] as bs '[i]
    )
    => HSetI HSmallArray a b as bs i where

    hsetI fa harrf = unsafeSetIndex harrf (getSNat @i) fa
    {-# inline hsetI #-}


instance HIxed HSmallArray as where
    hix i = L.lens (`indexViaSubseq` i) (`setIndexViaSubseq` i)
    {-# inline hix #-}
    hix' i = L.lens (`index` i) (`setIndex` i)
    {-# inline hix' #-}


instance HSingleton HSmallArray where
    hsingleton = L.iso (\(HSmallArray afas) -> unsafeCoerce (SA.indexSmallArray afas 0))
                       (\fa -> HSmallArray (SA.smallArrayFromListN 1 [unsafeCoerce fa]))
    {-# inline hsingleton #-}


instance HMonoid HSmallArray where
    hempty = HSmallArray mempty
    {-# noinline hempty #-}

    happend (HSmallArray as) (HSmallArray bs) = HSmallArray (as <> bs)
    {-# noinline happend #-}

    hcons fa (HSmallArray arr) = HSmallArray $ SA.runSmallArray do
        marr' <- SA.newSmallArray (SA.sizeofSmallArray arr + 1) (uninitializedElement "hcons")
        SA.writeSmallArray marr' 0 $! unsafeCoerce fa
        SA.copySmallArray marr' 1 arr 0 (SA.sizeofSmallArray arr)
        return marr'
    {-# noinline hcons #-}

    hsnoc (HSmallArray arr) fa = HSmallArray $ SA.runSmallArray do
        marr' <- SA.newSmallArray (SA.sizeofSmallArray arr + 1) (uninitializedElement "hcons")
        SA.copySmallArray marr' 0 arr 0 (SA.sizeofSmallArray arr)
        SA.writeSmallArray marr' (SA.sizeofSmallArray arr) $! unsafeCoerce fa
        return marr'
    {-# noinline hsnoc #-}


instance KnownLength as => HCreate HSmallArray as where
    hcreateA = createA getSNat
    {-# inline hcreateA #-}


instance HFunctor HSmallArray as where
    himap h harrf =
        create (size harrf) \i -> h i (index harrf i)
    {-# inline himap #-}


instance HApply HSmallArray as where
    hizipWith h harrf harrg =
        create (size harrf) \i -> h i (index harrf i) (index harrg i)
    {-# inline hizipWith #-}


instance HFoldable HSmallArray as where
    hifoldr f z harr =
        foldrNatInts (size harr) (\i r -> f i (index harr i) r) z
    {-# inline hifoldr #-}

    hifoldr2 f z harrf harrg =
        foldrNatInts (size harrf) (\i r -> f i (index harrf i) (index harrg i) r) z
    {-# inline hifoldr2 #-}


instance HTraversable HSmallArray as where
    hitraverse h harrf =
        createA (size harrf) \i -> h i (index harrf i)
    {-# inline hitraverse #-}

    hitraverse2 h harrf harrg =
        createA (size harrf) \i -> h i (index harrf i) (index harrg i)
    {-# inline hitraverse2 #-}


instance KnownLength as => HDistributive HSmallArray as



instance
    ( KnownPeanos is
    , KnownLength ss
    , IndexAll rs is ~ ss
    )
    => HSubsetI HSmallArray ss rs is where

    hgetSubsetI = getSubset @is
    {-# inline hgetSubsetI #-}
    hsetSubsetI = setSubset @is
    {-# inline hsetSubsetI #-}


instance
    ( ReplaceSubseqI ss ss' rs rs' is
    -- ReplaceSubseqWithError ss ss' rs rs'
    --, is ~ IndexesOfSubseq ss rs
    --, IndexAll rs is ~ ss
    , KnownLength ss
    , KnownLength rs'
    , KnownPeanos is
    )
    => HSubseqI HSmallArray ss ss' rs rs' is where

    hsubseqI = L.lens (getSubseq @is) \(HSmallArray ars) (HSmallArray ass') ->
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
    {-# inlinable hsubseqI #-}


_testSubseqInstance :: ()
_testSubseqInstance = testSubseqInstance @HSmallArray


instance
    ( ReplaceSubseqI ss '[] rs rs' is
    -- ReplaceSubseqWithError ss '[] rs rs'
    --, is ~ IndexesOfSubseq ss rs
    , KnownLength ss
    , KnownLength rs
    , KnownLength rs'
    , KnownPeanos is
    )
    => HQuotientI HSmallArray ss rs rs' is where

    hsubseqSplitI = L.iso
        (\(HSmallArray ars) ->
            let
              split :: Int -> [Any] -> [Int] -> ([Any], [Any])
              split !_ rs [] = ([], rs)

              split !i (r : rs) jjs@(j : js)
                | i == j    = case split (i+1) rs js  of (!ss, !rs') -> (r : ss, rs')
                | otherwise = case split (i+1) rs jjs of (!ss, !rs') -> (ss, r : rs')

              split !_ [] (_:_) = error "hsubseqSplitI @HSmallArray: split: the impossible happened"
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

            merge !_ [] (_:_) _ = error "hsubseqSplitI @HSmallArray: merge: the impossible happened"
            merge !_ (_:_) [] _ = error "hsubseqSplitI @HSmallArray: merge: the impossible happened"
          in
            HSmallArray $ SA.smallArrayFromListN (peanoInt @(Length rs)) $
                merge 0 (peanoInts @is) (toList ass) (toList ars'))
    {-# inlinable hsubseqSplitI #-}


instance KnownLength as => HConv HList.HList HSmallArray as where
    hconv :: forall f. HList.HList f as -> HSmallArray f as
    hconv hlist = HSmallArray $ SA.runSmallArray do
        marr :: SA.SmallMutableArray s Any
            <- SA.newSmallArray (peanoInt @(Length as)) (uninitializedElement "hconv @HList")

        let go :: Int -> HList.HList f bs -> ST s ()
            go !_ HList.HNil        = return ()
            go !i (fa HList.:& fas) = do
                SA.writeSmallArray marr i $! unsafeCoerce fa
                go (i+1) fas

        go 0 hlist
        return marr
    {-# inlinable hconv #-}


$(concat <$> forM [1..16] \n -> do
    cxt <- htupleInstanceContext n

    [d|
        instance TupleView HSmallArray $(gen_listTy cxt) where
            htupleWith  h arr =
                $(gen_tupExp' cxt \i ty _ -> [| h @($ty) (index arr (getSNat @($(peanoTys !! i)))) |])
            {-# inline htupleWith #-}
            htupleWithC h arr =
                $(gen_tupExp' cxt \i ty _ -> [| h @($ty) (index arr (getSNat @($(peanoTys !! i)))) |])
            {-# inline htupleWithC #-}

            fromHTuple $(gen_tupPat cxt) =
                unsafeHSmallArrayFromListN (getSNat @($(peanoTys !! n))) $
                    $(TH.listE [ [e| unsafeCoerce $aE |] | aE <- gen_aExps cxt])
            {-# noinline fromHTuple #-}
      |])
