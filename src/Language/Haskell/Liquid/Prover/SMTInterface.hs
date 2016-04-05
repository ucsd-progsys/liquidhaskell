module Language.Haskell.Liquid.Prover.SMTInterface where

import Language.Fixpoint.Smt.Interface 

import Language.Fixpoint.Types

makeContext :: FilePath -> [(Symbol, Sort)] -> IO Context 
makeContext = makeZ3Context

checkValid :: Context -> [Expr] -> Expr -> IO Bool
checkValid me is q = checkValidWithContext me [] (pAnd is) q

assert :: Context -> Expr -> IO ()
assert =  smtAssert
