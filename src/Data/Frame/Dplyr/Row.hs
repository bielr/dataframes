{-# language AllowAmbiguousTypes #-}
{-# language ImplicitParams #-}
{-# language InstanceSigs #-}
{-# language UndecidableInstances #-}
module Data.Frame.Dplyr.Row
  (
  -- Generic operations on different record representations
    untagged
  , cell
  , field
  , get
  , val
  , give

  -- ss is subsequence of rs if RImage ss rs is strictly monotone
  , rsubseq_
  , rsubseq

  -- special case: if RSubseq ss '[] rs rs', we can split rs into ss and rs'
  , rquotient
  , rquotientSplit
  , rquotientSplit'

  -- type-changing rsubset-related lenses
  , over_rsubset
  , rsubset_
  , rsubset
  , rreorder

  -- zipping/unzipping
  , ZipNamesTup
  , unzipped
  , unzipAs
  , zipped
  , zipAs

  -- field renaming
  , rrename
  ) where

import Control.Lens (Iso, Iso', Lens)
import Control.Lens qualified as L

import Data.Vinyl.Core (Rec(..))
import Data.Vinyl.FromTuple qualified as VX
import Data.Vinyl.XRec      qualified as VX

import Data.Frame.Field
import Data.Frame.Row
import Data.Frame.Types

import Data.Vinyl.Extra qualified as VE
import Data.Vinyl.Extra.TypeLevel (DeleteAll)


-- field access

cell :: RSingleton rec
     => Iso (Row rec '[ '(s, a)]) (Row rec '[ '(s, b)]) a b
cell = VE.rsingleton . untagged
{-# inline cell #-}


field :: forall i s a b col col' cols cols' rec.
    ( FieldSpec cols i col
    , col ~ '(s ,a)
    , col' ~ '(s, b)
    , RReplace rec col col' cols cols'
    )
    => Lens (Row rec cols) (Row rec cols') a b
field = VE.rlens @col . untagged
{-# inline field #-}


get :: forall i s a col cols rec.
    ( FieldSpec cols i col
    , RElem rec col cols
    , col ~ '(s, a)
    )
    => Row rec cols
    -> a
get = L.view (field @col)
{-# inline get #-}


val :: forall i s a col cols rec.
    ( FieldSpec cols i col
    , RElem rec col cols
    , col ~ '(s, a)
    , ?row :: Row rec cols
    )
    => a
val = get @col (?row)
{-# inline val #-}


give :: ((?row :: Row rec cols) => a) -> Row rec cols -> a
give a row =
    let ?row = row
    in  a
{-# inline give #-}


-- rsubseq lenses

rsubseq_ :: forall ss ss' rs rs' rec f.
    RSubseq rec ss ss' rs rs'
    => Lens (rec f rs) (rec f rs') (rec f ss) (rec f ss')
rsubseq_ = VE.rsubseq
{-# inline rsubseq_ #-}


rsubseq :: forall i ss' ss rs rs' rec f.
    ( FieldSpec rs i ss
    , RSubseq rec ss ss' rs rs'
    )
    => Lens (rec f rs) (rec f rs') (rec f ss) (rec f ss')
rsubseq = rsubseq_
{-# inline rsubseq #-}


-- special case for quotients and splitting records

rquotient :: forall i ss rs q rec f.
    ( FieldSpec rs i ss
    , RMonoid rec
    , RQuotient rec ss rs q
    )
    => rec f rs
    -> rec f q
rquotient = L.set (VE.rsubseq @ss) VE.rempty
{-# inline rquotient #-}


rquotientSplit :: forall i ss rs q rec f.
    ( FieldSpec rs i ss
    , RQuotient rec ss rs q
    )
    => Iso' (rec f rs) (rec f ss, rec f q)
rquotientSplit = VE.rsubseqSplit
{-# inline rquotientSplit #-}


rquotientSplit' :: forall i ss' ss rs rs' q q' rec f.
    ( FieldSpec rs i ss
    , RQuotient rec ss  rs  q
    , RQuotient rec ss' rs' q'
    )
    => Iso (rec f rs) (rec f rs') (rec f ss, rec f q) (rec f ss', rec f q')
rquotientSplit' = L.iso split unsplit'
  where
    split = L.view (rquotientSplit @ss)
    unsplit' = L.review (rquotientSplit @ss')
{-# inline rquotientSplit' #-}


-- type-changing rsubset-related lenses

over_rsubset :: forall ss ss' rs rec.
    ( RSubset rec ss rs
    , RSubset rec (DeleteAll ss rs) rs
    , REquiv rec (ss ++ DeleteAll ss rs) rs
    , RMonoid rec
    )
    => (Row rec ss -> Row rec ss')
    -> Row rec rs
    -> Row rec (ss' ++ DeleteAll ss rs)
over_rsubset f rec =
    f (VE.rcast @ss rec) `VE.rappend` VE.rcast @(DeleteAll ss rs) rec
{-# inline over_rsubset #-}


rsubset_ :: forall ss ss' rs rec.
    ( RSubset rec ss rs
    , RSubset rec (DeleteAll ss rs) rs
    , RSubset rec (ss ++ DeleteAll ss rs) rs
    , RMonoid rec
    )
    => Lens
        (Row rec rs) (Row rec (ss' ++ DeleteAll ss rs))
        (Row rec ss) (Row rec ss')
rsubset_ = L.lens (VE.rcast @ss) (\rec ss -> ss `VE.rappend` VE.rcast @(DeleteAll ss rs) rec)
{-# inline rsubset_ #-}


rsubset :: forall is ss ss' rs rec.
    ( FieldSpec rs is ss
    , RSubset rec ss rs
    , RSubset rec (DeleteAll ss rs) rs
    , RSubset rec (ss ++ DeleteAll ss rs) rs
    , RMonoid rec
    )
    => Lens
        (Row rec rs) (Row rec (ss' ++ DeleteAll ss rs))
        (Row rec ss) (Row rec ss')
rsubset = rsubset_
{-# inline rsubset #-}


rreorder :: forall rs' rs rec. REquiv rec rs rs' => Row rec rs -> Row rec rs'
rreorder = VE.rcast
{-# inline rreorder #-}


-- zipping/unzipping

type family ZipNamesTup (ss :: [Symbol]) (t :: Type) :: FieldsK where
    ZipNamesTup '[]                         ()                = '[]
    ZipNamesTup '[sa,sb]                    (a,b)             = '[ '(sa,a), '(sb,b)]
    ZipNamesTup '[sa,sb,sc]                 (a,b,c)           = '[ '(sa,a), '(sb,b), '(sc,c)]
    ZipNamesTup '[sa,sb,sc,sd]              (a,b,c,d)         = '[ '(sa,a), '(sb,b), '(sc,c), '(sd,d)]
    ZipNamesTup '[sa,sb,sc,sd,se]           (a,b,c,d,e)       = '[ '(sa,a), '(sb,b), '(sc,c), '(sd,d), '(se,e)]
    ZipNamesTup '[sa,sb,sc,sd,se,sf]        (a,b,c,d,e,f)     = '[ '(sa,a), '(sb,b), '(sc,c), '(sd,d), '(se,e), '(sf,f)]
    ZipNamesTup '[sa,sb,sc,sd,se,sf,sg]     (a,b,c,d,e,f,g)   = '[ '(sa,a), '(sb,b), '(sc,c), '(sd,d), '(se,e), '(sf,f), '(sg,g)]
    ZipNamesTup '[sa,sb,sc,sd,se,sf,sg,sh]  (a,b,c,d,e,f,g,h) = '[ '(sa,a), '(sb,b), '(sc,c), '(sd,d), '(se,e), '(sf,f), '(sg,g), '(sh,h)]


unzipped :: forall is' s a r ss' tss' tss'_tup.
    ( NameSpec is' ss'
    , r ~ '(s, a)
    , tss' ~ ZipNamesTup ss' tss'_tup
    , tss'_tup ~ VX.ListToHKDTuple Field tss'
    , VX.IsoXRec Field tss'
    , VX.TupleXRec Field tss'
    )
    => Iso
        (Rec Field '[r]) (Rec Field tss')
        a                tss'_tup
unzipped = L.iso (\(Field a :& RNil) -> a) VX.xrec
{-# inline unzipped #-}


unzipAs :: forall is' s a r ss' tss' tss'_tup.
    ( NameSpec is' ss'
    , r ~ '(s, a)
    , tss' ~ ZipNamesTup ss' tss'_tup
    , tss'_tup ~ VX.ListToHKDTuple Field tss'
    , VX.IsoXRec Field tss'
    , VX.TupleXRec Field tss'
    , a ~ tss'_tup
    )
    => Rec Field '[r]
    -> Rec Field tss'
unzipAs = L.over (unzipped @is') id
{-# inline unzipAs #-}


zipped :: forall i' s' r' ss ss_tup f.
    ( NameSpec i' s'
    , ss_tup ~ VX.ListToHKDTuple f ss
    , VX.IsoHKD f r'
    , VX.IsoXRec f ss
    , VX.TupleXRec f ss
    )
    => Iso
        (Rec f ss) (Rec f '[r'])
        ss_tup     (VX.HKD f r')
zipped = L.iso VX.ruple (\fb -> VX.unHKD fb :& RNil)
{-# inline zipped #-}


zipAs :: forall i' s' r' ss ss_tup f.
    ( NameSpec i' s'
    , ss_tup ~ VX.ListToHKDTuple f ss
    , VX.IsoHKD f r'
    , VX.IsoXRec f ss
    , VX.TupleXRec f ss
    , VX.HKD f r' ~ ss_tup
    )
    => Rec f ss
    -> Rec f '[r']
zipAs = L.over (zipped @i') id
{-# inline zipAs #-}


-- field renaming

rrename :: forall i i' s s' a r r' rs rs' rec.
    ( FieldSpec rs i r
    , NameSpec i' s'
    , r ~ '(s, a)
    , r' ~ '(s', a)
    , RReplace rec r r' rs rs'
    )
    => Row rec rs
    -> Row rec rs'
rrename = L.over (VE.rlens @r @r') (L.view renamed)
{-# inline rrename #-}
