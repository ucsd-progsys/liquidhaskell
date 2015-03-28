{-# LANGUAGE TupleSections #-}

module Language.Fixpoint.Test where

import           Language.Fixpoint.Interface
import           Language.Fixpoint.Parse
import           Language.Fixpoint.PrettyPrint
import           Language.Fixpoint.Types
import           Text.PrettyPrint.HughesPJ

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

f5 :: Test
f5 = (6, Safe, rr "(((((((newCount /= oldCount) && (lock == 0)) || ((newCount == oldCount) && (lock == 1)))) && (newCount /= oldCount)) => (((0 < newCount) => (((((newCount - 1) /= newCount))))) && ((not ((0 < newCount))) => ((((newCount == newCount))))))))")

f6 :: Test
f6 = (7, Safe, rr "(((((newCount /= oldCount) && (lock == 0)) || ((newCount == oldCount) && (lock == 1))) && (newCount /= oldCount)) => (((0 < newCount) => ((newCount - 1) /= newCount)) && ((not ((0 < newCount))) => (newCount == newCount))))")

f7 :: Pred
f7 = rr s7
s7 = "((((newCount /= oldCount))) && (((((newCount /= oldCount) && (lock == 0)) || ((newCount == oldCount) && (lock == 1))) && (newCount /= oldCount)) => (((0 < newCount) => (((((newCount - 1) /= newCount) && (0 == 0)) || (((newCount - 1) == newCount) && (0 == 1))))) && ((not ((0 < newCount))) => ((((newCount /= newCount) && (1 == 0)) || ((newCount == newCount) && (1 == 1))))))))"

s7' = show $ pprint f7

f7' :: Pred
f7' = rr s7'

f8 :: Test
f8 = (9, Safe, rr "(((((newCount /= oldCount) && (lock == 0)) || ((newCount == oldCount) && (lock == 1))) && (newCount /= oldCount)) => (((0 < newCount) => ((((newCount - 1) /= newCount) && (0 == 0)) || (((newCount - 1) == newCount) && (0 == 1)))) && ((not ((0 < newCount))) => (((newCount /= newCount) && (1 == 0)) || ((newCount == newCount) && (1 == 1))))))")


s7'' = "((newCount /= oldCount) && (((((newCount /= oldCount) && (lock == 0)) || ((newCount == oldCount) && (lock == 1))) && (newCount /= oldCount)) => (((0 < newCount) => ((((newCount - 1) /= newCount) && (0 == 0)) || (((newCount - 1) == newCount) && (0 == 1)))) && ((not ((0 < newCount))) => (((newCount /= newCount) && (1 == 0)) || ((newCount == newCount) && (1 == 1)))))))"

s8 = "((((newCount /= oldCount))) && (((((newCount /= oldCount) && (lock == 0)) || ((newCount == oldCount) && (lock == 1))) && (newCount /= oldCount)) => (((0 < newCount) => (((((newCount - 1) /= newCount) && (0 == 0)) || (((newCount - 1) == newCount) && (0 == 1))))) && ((not ((0 < newCount))) => ((((newCount /= newCount) && (1 == 0)) || ((newCount == newCount) && (1 == 1))))))))"


-- f6 :: Pred
-- f6 = rr "(&& [|| [ && [(newCount != oldCount); (lock = 0)];  && [(newCount = oldCount); (lock = 1)]];
--              (newCount != oldCount)
--              ]
--           => && [((0 < newCount) => ((newCount - 1) != newCount));
--                  ((~ ((0 < newCount))) => (newCount = newCount))])"

env p = map (, FInt) (syms p)
