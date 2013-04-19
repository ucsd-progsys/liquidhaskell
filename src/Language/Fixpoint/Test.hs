{-# LANGUAGE TupleSections #-}

module Language.Fixpoint.Test where 

import Language.Fixpoint.Parse
import Language.Fixpoint.Types
import Language.Fixpoint.Interface

runTest (l, r, p) = do r'    <- checkValid l (env p) p
                       return $ r' == r

type Test = (Int, FixResult Int, Pred)

f0, f0' :: Test 
f0  = (0, Safe,       rr "0 < 10")
f0' = (1, Unsafe [1], rr "0 > 10")

f1, f1' :: Test 
f1  = (2, Safe,       rr "(((x = 0) && (y = 5)) => (x < y))")
f1' = (3, Unsafe [3], rr "(((x = 0) && (y = 5)) => (x > y))")

f2, f2' :: Test 
f2  = (4, Safe,       rr "(((x = y) && (x1 = x + 1) && (y1 = y + 1)) => (x1 = y1))")
f2' = (5, Unsafe [5], rr "(((x < y) && (x1 = x + 1) && (y1 = y + 1)) => (x1 = y1))")

env p = map (, FInt) (syms p)
