{-# language TemplateHaskell #-}
module Data.Heterogeneous.HTuple.HTuple where

import GHC.Tuple (Solo)
import Data.Heterogeneous.TypeLevel
import Language.Haskell.TH qualified as TH


$(do
    let tupleTyCon = TH.mkName "TupleTyCon"
    nName <- TH.newName "n"
    let nVarT = TH.varT nName
    tName <- TH.newName "t"

    let toPeanoT 0 = [t| 'Zero |]
        toPeanoT k = [t| 'Succ $(toPeanoT (k-1)) |]

        tupleT 1 = [t| Solo |]
        tupleT k = TH.tupleT k

    let nBndr :: TH.Q (TH.TyVarBndr ())
        nBndr = return $ TH.kindedTV nName (TH.ConT ''Peano)

        tupleTyConSig :: TH.DecQ
        tupleTyConSig =
            -- type TupleTyCon :: forall (n :: Peano) -> NAryTyConK n Type Type
            TH.kiSigD tupleTyCon $
                TH.forallVisT [nBndr] $
                    [t| NAryTyConK $nVarT Type Type |]

        tyFam :: TH.DecQ
        tyFam =
            -- type family TupleTyCon n = t | t -> n
            TH.closedTypeFamilyD tupleTyCon [TH.plainTV nName]
                (TH.tyVarSig (TH.plainTV tName))
                (Just (TH.injectivityAnn tName [nName])) $
                    flip map [0..62] \n ->
                        TH.tySynEqn Nothing
                            (TH.appT (TH.conT tupleTyCon) (toPeanoT n))
                            (tupleT n)

    sequence [tupleTyConSig, tyFam])


type TupleOf :: [Type] -> Type
type TupleOf as = ApplyTyCon as (TupleTyCon (Length as))


type HTuple :: forall k. HTyConK k
newtype HTuple f as = HTuple { getHTuple :: TupleOf (Map f as) }


type IsTupleOf :: [Type] -> Type -> Constraint
type IsTupleOf as = AppliedTyCon as (TupleTyCon (Length as))

