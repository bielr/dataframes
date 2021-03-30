module Data.Heterogeneous.HTuple
    ( module Exports
    , htupleCo
    ) where

import Data.Functor.Identity
import Data.Type.Coercion
import Data.Type.Equality

import Data.Heterogeneous.Class.HCoerce (type (:~>:))
import Data.Heterogeneous.HTuple.Types as Exports
import Data.Heterogeneous.HTuple.Instances ()

import Unsafe.Coerce


htupleCo :: forall as t. IsTupleOf as t => t :~>: HTuple Identity as
htupleCo =
    case unsafeCoerce (Refl @t) :: t :~: HTuple Identity as of
        Refl -> Coercion
