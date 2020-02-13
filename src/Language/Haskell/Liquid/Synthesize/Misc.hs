{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module Language.Haskell.Liquid.Synthesize.Misc where

import qualified Language.Fixpoint.Types        as F 


import           Control.Monad.State.Lazy

import           CoreSyn
import           TyCoRep 
import           Text.PrettyPrint.HughesPJ (text, Doc, vcat, ($+$))
import           Language.Haskell.Liquid.Synthesize.GHC
import           Language.Haskell.Liquid.GHC.TypeRep
import           Text.PrettyPrint.HughesPJ ((<+>), text, char, Doc, vcat, ($+$))
import           Language.Fixpoint.Types


isFunction :: Type -> Bool
isFunction FunTy{}        = True 
isFunction (ForAllTy _ t) = True -- isFunction t 
isFunction _              = False

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


composeM :: Monad m => (a -> m b) -> (b -> c) -> a -> m c
composeM f g x = do 
    mx <- f x
    return (g mx)

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

showEmem :: (Show a1, Show a2) => [(Type, a1, a2)] -> String
showEmem  emem = show $ showEmem' emem

showEmem' :: (Show a1, Show a2) => [(Type, a1, a2)] -> [(String, String, String)]
showEmem' emem = map (\(t, e, i) -> (show e, showTy t, show i)) emem

exprmemToExpr :: [(a2, CoreExpr, Int)] -> String
exprmemToExpr em = show $ map (\(_, e, i) -> show (fromAnf e, i) ++ " * ") em 

showCand :: (a, (Type, b)) -> (String, b)
showCand (_, (t, v)) = (showTy t, v)

showCands :: [(a, (Type, b))] -> [(String, b)]
showCands = map showCand

notrace :: String -> a -> a 
notrace _ a = a 

instance PPrint AltCon

showCoreAlt :: CoreAlt -> String
showCoreAlt (DataAlt altCon, vars, expr) = 
  " For " ++ show altCon ++ " vars " ++ show vars ++ " expr " ++ show expr
showCoreAlt _ = " No! "

showCoreAlts :: [CoreAlt] -> String
showCoreAlts alts = concat (map showCoreAlt alts)