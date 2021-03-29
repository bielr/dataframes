{-# language DeriveGeneric #-}
{-# language UndecidableInstances #-}
{-# language TemplateHaskell #-}
module Data.Heterogeneous.HList where

import GHC.TypeLits

import Control.Applicative (liftA2)
import Control.Lens.Type
import Control.Lens qualified as L
import Data.Hashable
import Data.Hashable.Lifted (Hashable1, hashWithSalt1)
import Data.Profunctor.Unsafe
import Data.Traversable (forM)

import Data.Heterogeneous.Constraints
import Data.Heterogeneous.Class.Member
import Data.Heterogeneous.Class.HApply
import Data.Heterogeneous.Class.HCreate
import Data.Heterogeneous.Class.HFoldable
import Data.Heterogeneous.Class.HFunctor
import Data.Heterogeneous.Class.HMonoid
import Data.Heterogeneous.Class.HTraversable
import Data.Heterogeneous.Class.Subseq
import Data.Heterogeneous.Class.TupleView
import Data.Heterogeneous.Functors
import Data.Heterogeneous.HTuple (HTuple(..))
import Data.Heterogeneous.HTuple.TH
import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.TypeLevel.Subseq



type HList :: forall k. HTyConK k

data HList f as where
    HNil :: HList f '[]
    (:&) :: !(f a) -> !(HList f as) -> HList f (a ': as)

infixr 5 :&


hhead :: Lens (HList f (a ': as)) (HList f (b ': as)) (f a) (f b)
hhead f (a :& as) = (:& as) <$> f a


htail :: Lens (HList f (a ': as)) (HList f (a ': bs)) (HList f as) (HList f bs)
htail f (a :& as) = (a :&) <$> f as


huncons :: HList f (a ': as) -> (f a, HList f as)
huncons (a :& as) = (a, as)


hconsed :: Iso (f a, HList f as) (g b, HList g bs) (HList f (a ': as)) (HList g (b ': bs))
hconsed = L.iso (uncurry (:&)) huncons


hunconsed :: Iso (HList f (a ': as)) (HList g (b ': bs)) (f a, HList f as) (g b, HList g bs)
hunconsed = L.iso huncons (uncurry (:&))


after :: Profunctor p
    => LensLike (L.Context s a) s' a' s a
    -> Over p f s  t a  b
    -> Over p f s' t a' b
after ll l pa'fb s' =
    case ll (L.Context id) s' of
      L.Context aa' s -> l (lmap aa' pa'fb) s


preserving :: (Functor f, Profunctor p, Profunctor q)
    => L.AnIso (g t) (g b) t' b'
    -> Optical p q (Compose f g) s t  a b
    -> Optical p q f             s t' a b'
preserving hylo l =
    L.withIso hylo \alg coalg ->
        rmap (fmap alg .# getCompose) . l . rmap (Compose #. fmap coalg)


deriving stock instance FoldConstraints (Map (ComposeC Eq f) as)
    => Eq (HList f as)


deriving stock instance
    ( FoldConstraints (Map (ComposeC Eq f) as)
    , FoldConstraints (Map (ComposeC Ord f) as)
    )
    => Ord (HList f as)


deriving stock instance FoldConstraints (Map (ComposeC Show f) as)
    => Show (HList f as)


instance (Hashable1 f, FoldConstraints (Map Hashable as))
    => Hashable (HList f as) where
    hashWithSalt = go
      where
        go :: FoldConstraints (Map Hashable bs) => Int -> HList f bs -> Int
        go !salt'        HNil = salt'
        go !salt' (fa :& fas) = go (hashWithSalt1 salt' fa) fas



instance HSingleton HList where
    hsingleton = L.iso (\(fa :& HNil) -> fa) (:& HNil)
    {-# inline hsingleton #-}


instance HMonoid HList where
    hempty = HNil
    {-# inline hempty #-}

    happend HNil      bs = bs
    happend (a :& as) bs = a :& happend as bs
    {-# inline happend #-}

    hcons = (:&)
    {-# inline hcons #-}


instance HCreate HList '[] where
    hcreateA _ = pure HNil
    {-# inline hcreateA #-}


instance HCreate HList as => HCreate HList (a ': as) where
    hcreateA gf = liftA2 (:&) (gf zeroNat) (hcreateA (gf . succNat))
    {-# inline hcreateA #-}


instance HFunctor HList as where
    hmap _ HNil        = HNil
    hmap h (fa :& fas) = h fa :& hmap h fas
    {-# inline hmap #-}


    himap :: forall f g.
        (forall i. i < Length as => SNat i -> f (as !! i) -> g (as !! i))
        -> HList f as
        -> HList g as
    himap h = go zeroNat
      where
        go :: forall j. SNat j -> HList f (Drop j as) -> HList g (Drop j as)
        go !_ HNil      = HNil
        go !j (a :& as) =
            assuming (eqDropIndex @j @as) $
            assuming (eqDropNext @j @as) $
            assuming (leDropLength @j @as) $
                h j a :& go (succNat j) as
    {-# inline himap #-}


instance HApply HList as where
    hzipWith _ HNil        HNil        = HNil
    hzipWith h (fa :& fas) (fb :& fbs) = h fa fb :& hzipWith h fas fbs
    {-# inline hzipWith #-}


    hizipWith :: forall f g h.
        (forall i. i < Length as => SNat i -> f (as !! i) -> g (as !! i) -> h (as !! i))
        -> HList f as
        -> HList g as
        -> HList h as
    hizipWith h = go zeroNat
      where
        go :: forall j. SNat j -> HList f (Drop j as) -> HList g (Drop j as) -> HList h (Drop j as)
        go !_ HNil      HNil      = HNil
        go !j (a :& as) (b :& bs) =
            assuming (eqDropIndex @j @as) $
            assuming (eqDropNext @j @as) $
            assuming (leDropLength @j @as) $
                h j a b :& go (succNat j) as bs
    {-# inline hizipWith #-}


instance HFoldable HList as where
    hfoldr _ z HNil = z
    hfoldr f z (fa :& fas) = f fa (hfoldr f z fas)
    {-# inline hfoldr #-}


    hfoldr2 _ z HNil        HNil        = z
    hfoldr2 f z (fa :& fas) (ga :& gas) = f fa ga (hfoldr2 f z fas gas)
    {-# inline hfoldr2 #-}


    hifoldr :: forall f r.
        (forall i. i < Length as => SNat i -> f (as !! i) -> r -> r)
        -> r
        -> HList f as
        -> r
    hifoldr f z = go zeroNat
      where
        go :: forall j. SNat j -> HList f (Drop j as) -> r
        go _ HNil        = z
        go j (fa :& fas) =
            assuming (eqDropIndex  @j @as) $
            assuming (eqDropNext   @j @as) $
            assuming (leDropLength @j @as) $
                f j fa (go (succNat j) fas)
    {-# inline hifoldr #-}


    hifoldr2 :: forall f g r.
        (forall i. i < Length as => SNat i -> f (as !! i) -> g (as !! i) -> r -> r)
        -> r
        -> HList f as
        -> HList g as
        -> r
    hifoldr2 f z = go zeroNat
      where
        go :: forall j. SNat j -> HList f (Drop j as) -> HList g (Drop j as) -> r
        go _ HNil        HNil        = z
        go j (fa :& fas) (ga :& gas) =
            assuming (eqDropIndex  @j @as) $
            assuming (eqDropNext   @j @as) $
            assuming (leDropLength @j @as) $
                f j fa ga (go (succNat j) fas gas)
    {-# inline hifoldr2 #-}


instance HTraversable HList as where
    htraverse _ HNil        = pure HNil
    htraverse h (fa :& fas) = liftA2 (:&) (h fa) (htraverse h fas)
    {-# inline htraverse #-}


    hitraverse :: forall f g h.
        Applicative h
        => (forall i. i < Length as => SNat i -> f (as !! i) -> h (g (as !! i)))
        -> HList f as
        -> h (HList g as)
    hitraverse h = go zeroNat
      where
        go :: forall j. SNat j -> HList f (Drop j as) -> h (HList g (Drop j as))
        go !_ HNil      = pure HNil
        go !j (a :& as) =
            assuming (eqDropIndex @j @as) $
            assuming (eqDropNext @j @as) $
            assuming (leDropLength @j @as) $
                liftA2 (:&) (h j a) (go (succNat j) as)
    {-# inline hitraverse #-}


    htraverse2 _ HNil HNil               = pure HNil
    htraverse2 h (fa :& fas) (ga :& gas) = liftA2 (:&) (h fa ga) (htraverse2 h fas gas)
    {-# inline htraverse2 #-}


    hitraverse2 :: forall f f' g h.
        Applicative h
        => (forall i. i < Length as => SNat i -> f (as !! i) -> f' (as !! i) -> h (g (as !! i)))
        -> HList f as
        -> HList f' as
        -> h (HList g as)
    hitraverse2 h = go zeroNat
      where
        go :: forall j. SNat j -> HList f (Drop j as) -> HList f' (Drop j as) -> h (HList g (Drop j as))
        go !_ HNil      HNil      = pure HNil
        go !j (a :& as) (b :& bs) =
            assuming (eqDropIndex @j @as) $
            assuming (eqDropNext @j @as) $
            assuming (leDropLength @j @as) $
                liftA2 (:&) (h j a b) (go (succNat j) as bs)
    {-# inline hitraverse2 #-}


instance TypeError
    ('Text "There is no HIxed instance for HList because performance is really bad for the most common use case. Use hlistIx manually instead")
    => HIxed HList as where
    hix' _ = error "No instance HIxed HList"
    hix _ = error "No instance HIxed HList"


hlistIx :: i < Length as => SNat i -> Lens' (HList f as) (f (as !! i))
hlistIx _ _ HNil = undefined
hlistIx i f (a :& as) =
    caseNat i
        ((:& as) <$> f a)
        ((a :&) <$> hlistIx (predNat i) f as)


-- insert ss' at head

instance
    ( ReplaceSubseqI '[] ss' rs rs' '[]
    , rs' ~ (ss' ++ rs)
    )
    => HSubseqI HList '[] ss' rs rs' '[] where

    hsubseqI f rs = (`happend` rs) <$> f HNil
    {-# inline hsubseqI #-}


instance rs' ~ rs => HQuotientI HList '[] rs rs' '[] where
    hsubseqSplitI = L.iso (\rs -> (HNil, rs)) (\(HNil, rs) -> rs)
    {-# inline hsubseqSplitI #-}


-- delete ss

instance
    ( HSubseqI HList ss '[] rs rs' dec_is'
    , DecSeq is' dec_is'
    --, IndexesOfSubseq ss (r ': rs) ~ is'
    , s ~ r
    )
    => HSubseqI HList (s ': ss) '[] (r ': rs) rs' ('Zero ': is') where

    hsubseqI = after htail (hsubseqI @HList @_ @_ @_ @_ @dec_is')
    {-# inline hsubseqI #-}


instance
    ( HQuotientI HList ss rs rs' dec_is'
    , DecSeq is' dec_is'
    --, IndexesOfSubseq ss (r ': rs) ~ is'
    , s ~ r
    )
    => HQuotientI HList (s ': ss) (r ': rs) rs' ('Zero ': is') where

    hsubseqSplitI =
        hunconsed
        . L.mapping (hsubseqSplitI @HList @_ @_ @_ @dec_is')
        . L.iso (uncurry consl) (L._1 huncons)
      where
        consl s (!ss, !rs') = (s :& ss, rs')
    {-# inline hsubseqSplitI #-}


-- replace nonempty ss with nonempty ss'

instance
    ( HSubseqI HList ss ss' rs rs' dec_is'
    , DecSeq is' dec_is'
    --, IndexesOfSubseq ss (r ': rs) ~ is'
    , s ~ r
    , s' ~ r'
    )
    => HSubseqI HList (s ': ss) (s' ': ss') (r ': rs) (r' ': rs') ('Zero ': is') where

    hsubseqI = preserving hconsed (after htail (hsubseqI @HList @_ @_ @_ @_ @dec_is'))
    {-# inline hsubseqI #-}


instance
    ( HSubseqI HList ss ss' rs rs' (i ': dec_is')
    , DecSeq is' dec_is'
    --, IndexesOfSubseq ss (r ': rs) ~ IncSeq (IndexesOfSubseq ss rs)
    , r ~ r'
    )
    => HSubseqI HList ss ss' (r ': rs) (r' ': rs') ('Succ i ': is') where

    hsubseqI = htail . hsubseqI @HList @_ @_ @_ @_ @(i ': dec_is')
    {-# inline hsubseqI #-}

_testSubseqInstance :: ()
_testSubseqInstance = testSubseqInstance @HList


instance
    ( HQuotientI HList ss rs rs' (i ': dec_is')
    , DecSeq is' dec_is'
    --, IndexesOfSubseq ss (r ': rs) ~ IncSeq (IndexesOfSubseq ss rs)
    , r ~ r'
    )
    => HQuotientI HList ss (r ': rs) (r' ': rs') ('Succ i ': is') where

    hsubseqSplitI =
        hunconsed
        . L.mapping (hsubseqSplitI @HList @_ @_ @_ @(i ': dec_is'))
        . L.iso (uncurry consr) (L._2 huncons)
      where
        consr r (!ss, !rs') = (ss, r :& rs')
    {-# inline hsubseqSplitI #-}



instance TupleView HList '[] where
    htupleWith _ HNil = HTuple ()
    htupleWithC _ HNil = HTuple ()
    fromHTuple (HTuple ()) = HNil


$(concat <$> forM [1..8] \n -> do
    cxt <- htupleInstanceContext n

    let recPat   = foldr (\a as -> [p| $a :& $as |]) [p| HNil |] (gen_aPats cxt)
        recExp g = foldr
                    (\(aTy, aE) as -> [| $(g aTy aE) :& $as |])
                    [| HNil |]
                    (zip (gen_aTys cxt) (gen_aExps cxt))

    [d|
        instance TupleView HList $(gen_listTy cxt) where
            htupleWith  h $recPat = $(gen_tupExp cxt \_ _ fa -> [| h $fa |])
            {-# inline htupleWith #-}
            htupleWithC h $recPat = $(gen_tupExp cxt \_ _ fa -> [| h $fa |])
            {-# inline htupleWithC #-}

            fromHTuple $(gen_tupPat cxt) = $(recExp \_ fa -> fa)
            {-# inline fromHTuple #-}
      |])
