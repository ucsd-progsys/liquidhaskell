{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module Language.Haskell.Liquid.Synthesize.Misc where

import qualified Language.Fixpoint.Types        as F 
import qualified Language.Fixpoint.Types.Config as F
import qualified Language.Fixpoint.Smt.Interface as SMT

import TyCoRep 
import           Control.Monad.State.Lazy

import           Text.PrettyPrint.HughesPJ ((<+>), text, char, Doc, vcat, ($+$))

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