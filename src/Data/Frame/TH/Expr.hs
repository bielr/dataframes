{-# language TemplateHaskellQuotes #-}
module Data.Frame.TH.Expr where

import Data.HashTable.IO qualified as HT
import GHC.Generics
import Data.Ratio (Ratio)
import Data.Word (Word8)
import Language.Haskell.TH.Syntax

import Data.Frame.Class (col)

import Control.Lens (Traversal', _Just, has, forMOf)
import Language.Haskell.TH.Lens (_LabelE)


class GHasExps g where
    gexps :: (Exp -> Bool) -> Traversal' (g p) Exp


instance GHasExps U1 where
    gexps _ _ = pure

instance HasExps a => GHasExps (K1 i a) where
    gexps stop f (K1 a) = K1 <$> exps stop f a

instance GHasExps f => GHasExps (M1 i c f) where
    gexps stop f (M1 fp) = M1 <$> gexps stop f fp

instance (GHasExps f, GHasExps g) => GHasExps (f :+: g) where
    gexps stop f = \case
        L1 fp -> L1 <$> gexps stop f fp
        R1 fp -> R1 <$> gexps stop f fp

instance (GHasExps f, GHasExps g) => GHasExps (f :*: g) where
    gexps stop f (fp :*: gp) = (:*:) <$> gexps stop f fp <*> gexps stop f gp


class HasExps a where
     exps :: (Exp -> Bool) -> Traversal' a Exp

     default exps :: (Generic a, GHasExps (Rep a)) => (Exp -> Bool) -> Traversal' a Exp
     exps stop f a = to <$> gexps stop f (from a)

instance HasExps Exp where
    exps stop f e
      | stop e    = f e
      | otherwise = to <$> gexps stop f (from e)

instance HasExps a => HasExps (Maybe a) where
    exps stop = _Just.exps stop

instance HasExps a => HasExps [a] where
    exps stop = traverse.exps stop

instance HasExps ()              where exps _ _ = pure
instance HasExps Name            where exps _ _ = pure
instance HasExps Char            where exps _ _ = pure
instance HasExps Int             where exps _ _ = pure
instance HasExps Word8           where exps _ _ = pure
instance HasExps Integer         where exps _ _ = pure
instance HasExps Bytes           where exps _ _ = pure
instance HasExps (Ratio Integer) where exps _ _ = pure

instance (HasExps a, HasExps b) => HasExps (a,b)
instance (HasExps a, HasExps b, HasExps c) => HasExps (a,b,c)

instance HasExps AnnTarget
instance HasExps Bang
instance HasExps Body
instance HasExps Callconv
instance HasExps Clause
instance HasExps Con
instance HasExps Dec
instance HasExps DerivClause
instance HasExps DerivStrategy
instance HasExps FamilyResultSig
instance HasExps FixityDirection
instance HasExps Foreign
instance HasExps FunDep
instance HasExps Guard
instance HasExps InjectivityAnn
instance HasExps Inline
instance HasExps Language.Haskell.TH.Syntax.Fixity
instance HasExps Language.Haskell.TH.Syntax.SourceStrictness
instance HasExps Language.Haskell.TH.Syntax.SourceUnpackedness
instance HasExps Lit
instance HasExps Match
instance HasExps ModName
instance HasExps Overlap
instance HasExps Pat
instance HasExps PatSynArgs
instance HasExps PatSynDir
instance HasExps Phases
instance HasExps Pragma
instance HasExps Range
instance HasExps Role
instance HasExps RuleBndr
instance HasExps RuleMatch
instance HasExps Safety
instance HasExps Specificity
instance HasExps Stmt
instance HasExps TyLit
instance HasExps TySynEqn
instance HasExps Type
instance HasExps TypeFamilyHead
instance HasExps a => HasExps (TyVarBndr a)


rowwise :: Q Exp -> Q Exp
rowwise qe = do
    e <- qe

    names :: HT.BasicHashTable String Name <- runIO $ HT.new

    e' <- forMOf (exps (has _LabelE)) e \(LabelE l) ->
        runIO (HT.lookup names l) >>= \case
            Just varName ->
                return (VarE varName)
            Nothing -> do
                varName <- newName l
                runIO $ HT.insert names l varName
                return (VarE varName)

    varNames <- runIO $ HT.toList names

    let binds =
          [ BindS
            (VarP varName)
            (AppTypeE (VarE 'col) (LitT (StrTyLit label)))
          | (label, varName) <- varNames
          ]

    return $ DoE Nothing $ binds ++ [NoBindS (AppE (VarE 'pure) e')]
