{-# LANGUAGE UndecidableInstances #-}
module Data.Heterogeneous.TypeLevel.Subseq
  ( IncSeq
  , DecSeq
  , IndexesOf
  , IndexesOfSubseq
  , IsSubsetWithError
  , IsSubseq
  , IsSubseqWithError
  , ReplaceSubseq
  , ReplaceSubseqWithError
  ) where

import Data.Proxy
import Type.Errors

import Data.Heterogeneous.TypeLevel.Kind
import Data.Heterogeneous.TypeLevel.Index
import Data.Heterogeneous.TypeLevel.Peano


-- (strictly) monotone Peano lists

type IncSeq :: [Peano] -> [Peano]

type family IncSeq is = dec_is | dec_is -> is where
    IncSeq '[] = '[]
    IncSeq (i ': is) = 'Succ i ': IncSeq is

type DecSeq is dec_is = IncSeq dec_is ~ is


type Monotone :: [Peano] -> Constraint
class Monotone is

instance Monotone '[]
instance (DecSeq is' dec_is', Monotone dec_is') => Monotone ('Zero ': is')
instance (DecSeq is' dec_is', Monotone (dec_i ': dec_is')) => Monotone ('Succ dec_i ': is')


-- ss is a subsequence (preserving order) of rs

type IndexesOfSubseq :: forall k. [k] -> [k] -> [Peano]
type family IndexesOfSubseq as bs where
    IndexesOfSubseq '[]       bs        = '[]
    IndexesOfSubseq (a ': as) (a ': bs) = 'Zero ': IncSeq (IndexesOfSubseq as bs)
    IndexesOfSubseq (a ': as) (b ': bs) = IncSeq (IndexesOfSubseq (a ': as) bs)


type ForcePeanos :: [Peano] -> ()
type family ForcePeanos is where
    ForcePeanos '[]             = '()
    ForcePeanos ('Zero   ': is) = ForcePeanos is
    ForcePeanos ('Succ i ': is) = ForcePeanos (i ': is)


type IndexesOfSubseqMonotoneError :: forall k. [k] -> [k] -> ErrorMessage
type IndexesOfSubseqMonotoneError as bs =
    'Text "The elements of "
    ':<>: 'ShowType as
    ':<>: 'Text " appear in a different order in "
    ':<>: 'ShowType bs


type IsSubsetWithError :: forall k. [k] -> [k] -> Constraint
type IsSubsetWithError ss rs =
    WhenStuck (ForcePeanos (IndexesOf ss rs))
      (DelayError (IndexesOfError ss rs))


type IsSubseq :: forall k. [k] -> [k] -> [Peano] -> Constraint

class is ~ IndexesOfSubseq ss rs => IsSubseq ss rs is | is rs -> ss

instance IsSubseq '[] rs '[]

instance
    ( IsSubseq ss rs dec_is
    , IncSeq dec_is ~ is
    , s ~ r
    ) => IsSubseq (s ': ss) (r ': rs) ('Zero ': is)

instance
    ( IsSubseq ss rs (i ': dec_is)
    , IncSeq dec_is ~ is
    , IndexesOfSubseq ss (r ': rs) ~ IncSeq (IndexesOfSubseq ss rs)
    ) => IsSubseq ss (r ': rs) ('Succ i ': is)


type IsSubseqWithError :: forall k. [k] -> [k] -> Constraint
type IsSubseqWithError ss rs =
    IfStuck (ForcePeanos (IndexesOf ss rs))
      (DelayError (IndexesOfError ss rs))
      (Pure (IfStuck (ForcePeanos (IndexesOfSubseq ss rs))
              (DelayError (IndexesOfSubseqMonotoneError ss rs))
              (Pure (IsSubseq ss rs (IndexesOfSubseq ss rs)))))


-- Replacing ss with ss' in rs yields rs'

type ReplaceSubseq :: forall k. [k] -> [k] -> [k] -> [k] -> [Peano] -> Constraint

class IsSubseq ss rs is => ReplaceSubseq ss ss' rs rs' is
    | is rs -> ss
    , is ss rs' -> rs
    , is ss' rs -> rs'


-- trivial case

instance (rs ~ rs')
    => ReplaceSubseq '[] '[] rs rs' '[]

-- insert ss' at head

instance
    ( ReplaceSubseq '[] ss' rs rs' '[]
    , s' ~ r'
    )
    => ReplaceSubseq '[] (s' ': ss') rs (r' ': rs') '[]

-- delete ss

instance
    ( ReplaceSubseq ss '[] rs rs' dec_is
    , IncSeq dec_is ~ is
    --, IndexesOfSubseq ss (r ': rs) ~ is
    , s ~ r
    )
    => ReplaceSubseq (s ': ss) '[] (r ': rs) rs' ('Zero ': is)

-- replace non-empty ss with non-empty ss'

instance
    ( ReplaceSubseq ss ss' rs rs' dec_is
    , IncSeq dec_is ~ is
    --, IndexesOfSubseq ss (r ': rs) ~ is
    , s ~ r
    , s' ~ r'
    )
    => ReplaceSubseq (s ': ss) (s' ': ss') (r ': rs) (r' ': rs') ('Zero ': is) where

instance
    ( ReplaceSubseq ss ss' rs rs' (i ': dec_is)
    , IncSeq dec_is ~ is
    , IndexesOfSubseq ss  (r ': rs) ~ IncSeq (IndexesOfSubseq ss rs)
    , r ~ r'
    )
    => ReplaceSubseq ss ss' (r ': rs) (r' ': rs') ('Succ i ': is) where


type ReplaceSubseqWithError :: forall k. [k] -> [k] -> [k] -> [k] -> Constraint
type ReplaceSubseqWithError ss ss' rs rs' =
    ( IsSubseqWithError ss rs
    , ReplaceSubseq ss ss' rs rs' (IndexesOfSubseq ss rs)
    )


-- tests

_testIsSubseq :: IsSubseqWithError ss rs => Proxy '(ss, rs)
_testIsSubseq = Proxy
  where
    _test1 = _testIsSubseq @'[] @'[]
    _test2 = _testIsSubseq @'[] @'[1,2,3]
    _test3 = _testIsSubseq @'[2,4] @'[1,2,3,4,5]


_testReplaceSubseq ::
    ReplaceSubseqWithError ss ss' rs rs'
    => Proxy '(ss, ss', rs)
_testReplaceSubseq = Proxy
  where
    _test1 = _testReplaceSubseq @'[] @'[1,2,3] @'[4,5,6] @'[1,2,3,4,5,6]
    _test2 = _testReplaceSubseq @'[1,2,3] @'[] @'[1,2,3,4,5,6] @'[4,5,6]
    _test3 = _testReplaceSubseq @'[5] @'[9,10] @'[1,2,3,4,5,6,7] @'[1,2,3,4,9,10,6,7]
    _test4 = _testReplaceSubseq @'[2,4,6] @'[1,3,5] @'[1,2,3,4,5,6] @'[1,1,3,3,5,5]

