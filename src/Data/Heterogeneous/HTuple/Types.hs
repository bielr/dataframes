{-# language AllowAmbiguousTypes #-}
{-# language QuantifiedConstraints #-}
{-# language TemplateHaskell #-}
{-# language UndecidableInstances #-}
module Data.Heterogeneous.HTuple.Types
  ( TupleTyCon
  , TupleLength
  , TupleTyConOf
  , TupleMembers
  , TupleOf
  , IsTupleOf
  , HTuple(..)
  ) where

import GHC.Tuple (Solo)
import Control.Monad (replicateM)
import Data.Foldable (foldl')
import Data.Type.Equality
import Language.Haskell.TH qualified as TH

import Data.Heterogeneous.TypeLevel


$(do
    let toPeanoT 0 = [t| 'Zero |]
        toPeanoT k = [t| 'Succ $(toPeanoT (k-1)) |]

        tupleT 1 = [t| Solo |]
        tupleT k = TH.tupleT k

    nName <- TH.newName "n"
    let nVarT = TH.varT nName

    fName <- TH.newName "f"

    let tupleTyCon = TH.mkName "TupleTyCon"
        tupleTyConTy = TH.conT tupleTyCon

        nBndr :: TH.Q (TH.TyVarBndr ())
        nBndr = return $ TH.kindedTV nName (TH.ConT ''Peano)

        tupleTyConSig :: TH.DecQ
        tupleTyConSig =
            -- type TupleTyCon :: forall (n :: Peano) -> NAryTyConK n Type Type
            TH.kiSigD tupleTyCon $
                TH.forallVisT [nBndr] $
                    [t| NAryTyConK $nVarT Type Type |]

        tupleTyConDef :: TH.DecQ
        tupleTyConDef =
            -- type family TupleTyCon n = f | f -> n
            TH.closedTypeFamilyD tupleTyCon [TH.plainTV nName]
                (TH.tyVarSig (TH.plainTV fName))
                (Just (TH.injectivityAnn fName [nName])) $
                    flip map [0..62] \n ->
                        TH.tySynEqn Nothing
                            [t| $tupleTyConTy $(toPeanoT n) |]
                            (tupleT n)

    tName <- TH.newName "t"

    aNames <- replicateM 64 (TH.newName "a")

    let aVarTs = map TH.varT aNames
        appliedTupleT k = foldl' TH.appT (tupleT k) (take k aVarTs)

    let tupleLength = TH.mkName "TupleLength"
        tupleLengthTy = TH.conT tupleLength

        tupleLengthSig :: TH.DecQ
        tupleLengthSig =
            -- type TupleLength :: Type -> Peano
            TH.kiSigD tupleLength [t| Type -> Peano |]

        tupleLengthDef :: TH.DecQ
        tupleLengthDef =
            -- type family TupleLength t where ...
            TH.closedTypeFamilyD tupleLength [TH.plainTV tName] TH.noSig Nothing $
                flip map [0..62] \n ->
                    TH.tySynEqn Nothing
                        [t| $tupleLengthTy $(appliedTupleT n) |]
                        (toPeanoT n)

    let tVarT = TH.varT tName

    let tupleTyConOf = TH.mkName "TupleTyConOf"
        tupleTyConOfTy = TH.conT tupleTyConOf

        tBndr :: TH.Q (TH.TyVarBndr ())
        tBndr = return $ TH.kindedTV tName (TH.ConT ''Type)

        tupleTyConOfSig :: TH.DecQ
        tupleTyConOfSig =
            -- type TupleTyConOf :: forall (t :: Type) -> NAryTyConK (TupleLength t) Type Type
            TH.kiSigD tupleTyConOf $
                TH.forallVisT [tBndr] $
                    [t| NAryTyConK ($tupleLengthTy $tVarT) Type Type |]

        tupleTyConOfDef :: TH.DecQ
        tupleTyConOfDef =
            -- type family TupleTyConOf t where ...
            TH.closedTypeFamilyD tupleTyConOf [TH.plainTV tName] TH.noSig Nothing $
                flip map [0..62] \n ->
                    TH.tySynEqn Nothing
                        [t| $tupleTyConOfTy $(appliedTupleT n) |]
                        [t| $tupleTyConTy $(toPeanoT n) |]

    asName <- TH.newName "as"

    let tupleMembers = TH.mkName "TupleMembers"
        tupleMembersTy = TH.conT tupleMembers

        tupleMembersSig :: TH.DecQ
        tupleMembersSig =
            -- type TupleMembers :: Type -> [Type]
            TH.kiSigD tupleMembers [t| Type -> [Type] |]

        tupleMembersDef :: TH.DecQ
        tupleMembersDef =
            -- type family TupleMemberTypes t = as | as -> t where ...
            TH.closedTypeFamilyD tupleMembers [TH.plainTV tName]
                (TH.tyVarSig (TH.plainTV asName))
                (Just (TH.injectivityAnn asName [tName])) $
                    flip map [0..62] \n ->
                        TH.tySynEqn Nothing
                            [t| $tupleMembersTy $(appliedTupleT n) |]
                            (foldr (\a as -> [t| $a ': $as |])
                                TH.promotedNilT
                                (take n aVarTs))

    sequence
        [ tupleTyConSig, tupleTyConDef
        , tupleLengthSig, tupleLengthDef
        , tupleTyConOfSig, tupleTyConOfDef
        , tupleMembersSig, tupleMembersDef
        ])


type TupleOf :: [Type] -> Type
type TupleOf as = ApplyTyCon as (TupleTyCon (Length as))


type IsTupleOf :: [Type] -> Type -> Constraint

class
    ( as ~ TupleMembers t
    , TupleTyConOf t ~~ TupleTyCon (Length as)
    , AppliedTyCon as (TupleTyCon (Length as)) t
    )
    => IsTupleOf as t | t -> as, as -> t

instance
    ( as ~ TupleMembers t
    , TupleTyConOf t ~~ TupleTyCon (Length as)
    , AppliedTyCon as (TupleTyCon (Length as)) t
    )
    => IsTupleOf as t


type HTuple :: forall k. HTyConK k
newtype HTuple f as = HTuple (TupleOf (Map f as))


deriving stock instance Eq (TupleOf (Map f as)) => Eq (HTuple f as)
deriving stock instance (Eq (TupleOf (Map f as)), Ord (TupleOf (Map f as))) => Ord (HTuple f as)
deriving stock instance Show (TupleOf (Map f as)) => Show (HTuple f as)
