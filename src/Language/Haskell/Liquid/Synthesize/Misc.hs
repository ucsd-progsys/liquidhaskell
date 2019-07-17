{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module Language.Haskell.Liquid.Synthesize.Misc where

import qualified Language.Fixpoint.Types        as F 
import qualified Language.Fixpoint.Types.Config as F
import qualified Language.Fixpoint.Smt.Interface as SMT


import           Control.Monad.State.Lazy

import CoreSyn (CoreExpr)
import qualified CoreSyn as GHC
import           TyCoRep 
import Language.Haskell.Liquid.Synthesize.Monad
import           Text.PrettyPrint.HughesPJ ((<+>), text, char, Doc, vcat, ($+$))
import           Language.Haskell.Liquid.Synthesize.GHC

-- can we replace it with Language.Haskell.Liquid.GHC.Misc.isBaseType ? 
isBasic :: Type -> Bool
isBasic TyConApp{}     = True
isBasic TyVarTy {}     = True
isBasic (ForAllTy _ t) = isBasic t
isBasic AppTy {}       = False 
isBasic LitTy {}       = False
isBasic _              = False


(<$$>) :: (Functor m, Functor n) => (a -> b) -> m (n a) -> m (n b)
(<$$>) = fmap . fmap

filterElseM :: Monad m => (a -> m Bool) -> [a] -> m [a] -> m [a]
filterElseM f as ms = do
    rs <- filterM f as
    if null rs then
        ms
    else
        return rs

-- Replaces    | old w   | new  | symbol name in expr.
substInFExpr :: F.Symbol -> F.Symbol -> F.Expr -> F.Expr
substInFExpr pn nn e = F.subst1 e (pn, F.EVar nn)


findM :: Monad m => (a -> m Bool) -> [a] -> m (Maybe a)
findM _ []     = return Nothing
findM p (x:xs) = do b <- p x ; if b then return (Just x) else findM p xs 

symbolExpr :: Type -> F.Symbol -> SM CoreExpr 
symbolExpr τ x = incrSM >>= (\i -> return $ F.notracepp ("symExpr for " ++ F.showpp x) $  GHC.Var $ mkVar (Just $ F.symbolString x) i τ)

----------------------------------------------------------------------------
----------------------------Printing----------------------------------------
----------------------------------------------------------------------------
solDelim :: String
solDelim = "\n*********************************************\n"

pprintMany :: (F.PPrint a) => [a] -> Doc
pprintMany xs = vcat [ F.pprint x $+$ text solDelim | x <- xs ]

showGoals :: [[String]] -> String
showGoals []             = ""
showGoals (goal : goals) = 
    show goal        ++ 
    "\n"             ++ 
    replicate 12 ' ' ++ 
    showGoals goals

takeExprs = map snd 