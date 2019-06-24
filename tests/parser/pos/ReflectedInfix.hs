module ReflectedInfix where
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}

import Language.Haskell.Liquid.ProofCombinators 
import Prelude hiding ((++))

{-@ infix ++ @-}
{-@ reflect ++ @-}
(++) :: [a]-> [a] -> [a] 
[] ++ ys = ys 
(x:xs) ++ ys = x : (xs ++ ys)

{-@ appendNilId :: xs:[a] -> { xs ++ [] = xs } @-}
appendNilId :: [a] -> Proof
appendNilId xs = undefined 

{-@ nilAppendId :: xs:[a] -> { [] ++ xs = xs } @-}
nilAppendId :: [a] -> Proof
nilAppendId xs = undefined 
