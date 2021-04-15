module Data.Frame.Types
  ( module Vinyl
  , module Exports

  -- Other Frame types
  , GroupedFrame(..)

  -- Constraint aliases
  , RElem, RReplace
  , RSubset, REquiv
  , RSubseq'
  ) where

import Data.Vinyl           as Vinyl (Rec)
import Data.Vinyl.Functor   as Vinyl ((:.), Compose(..))
import Data.Vinyl.Derived   as Vinyl (type (:::), FieldType)
import Data.Vinyl.TypeLevel as Vinyl (type (++), Fst, Snd, RIndex, RImage)

import Data.Frame.Column        as Exports (Col, ColIx)
import Data.Frame.Field         as Exports (Field)
import Data.Frame.Frame         as Exports (Frame)
import Data.Frame.Internal.Repr as Exports (KnownMajor, Major, SMajor, KnownRepr, Repr, SRepr)
import Data.Frame.Kind          as Exports
import Data.Frame.TypeIndex     as Exports
import Data.Indexer             as Exports (Indexer)

import Data.Vinyl.Extra.Class as Exports (RecElem, RecSubset,
                                          RSingleton, RMonoid, RNew, RConv, RTupled,
                                          RFunctor, RFoldable, RTraversable, RDistributive,
                                          RIxed, RSubseq, RQuotient)

import Data.Vinyl.Extra.SARec                 as Exports (SARec)
import Data.Vinyl.Extra.TypeLevel.Constraints as Exports

-- Grouped frames

newtype GroupedFrame p k rep rec f cols = GroupedFrame { getGroups :: p k (Frame rep rec f cols) }


-- Constraint aliases

type RElem rec col cols = RecElem rec col col cols cols

type RReplace = RecElem

type RSubset = RecSubset

type REquiv rec cols cols' = (RSubset rec cols cols', RSubset rec cols' cols)

type RSubseq' rec subs cols = RSubseq rec subs subs cols cols
