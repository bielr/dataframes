module Data.Heterogeneous.HTuple
    ( module Exports
    , htupleCo
    , htupleCoF
    ) where

import Control.Category ((<<<))
import Data.Functor.Identity
import Data.Type.Coercion
import Data.Type.Equality

import Data.Heterogeneous.Class.HCoerce
import Data.Heterogeneous.HTuple.Types as Exports
import Data.Heterogeneous.HTuple.Instances ()

import Unsafe.Coerce


htupleCo :: forall as t. IsTupleOf as t => t :~>: HTuple Identity as
htupleCo =
    case unsafeCoerce (Refl @t) :: t :~: HTuple Identity as of
        Refl -> Coercion


htupleCoF :: (HCoerce HTuple as, IsTupleOfF f as t) => t :~>: HTuple f as
htupleCoF =
    hIdLCo <<< hconOutCo <<< htupleCo
