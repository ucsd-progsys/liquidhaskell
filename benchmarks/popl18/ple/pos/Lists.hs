{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Lists where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (length, (++))

{-@ infixr ++ @-}


{-@ propConst1 :: () -> { (((C 1 Emp) ++ Emp) ++ Emp) == (C 1 Emp) } @-}
propConst1 :: () -> Proof
propConst1 _ = trivial 


{-@ automatic-instances propConst2 with 3 @-}
{-@ propConst2 :: () -> { (((C 1 (C 2 Emp)) ++ Emp) ++ Emp) == (C 1 (C 2 Emp)) } @-}
propConst2 :: () -> Proof
propConst2 _ = trivial 


{-@ automatic-instances propConst3 with 4 @-}
{-@ propConst3 :: () -> { (((C 1 (C 2 (C 3 Emp))) ++ Emp) ++ Emp) == (C 1 (C 2 (C 3 Emp))) } @-}
propConst3 :: () -> Proof
propConst3 _ = trivial 


prop :: a -> L a -> L a -> L a -> Proof 
{-@ prop :: x:a -> xs:L a -> ys:L a -> zs:L a 
         -> {((C x xs) ++ ys) ++ zs == C x ((xs ++ ys) ++ zs) } @-} 
prop x xs ys zs = trivial



data L a = Emp | C a (L a)
{-@ data L [length] a = Emp | C {x::a, xs :: L a } @-}

{-@ measure length @-}
length :: L a -> Int
{-@ length :: L a -> Nat @-}
length Emp        = 0
length (C _ xs) = 1 + length xs

{-@ axiomatize ++ @-}
(++) :: L a -> L a -> L a
Emp      ++ ys = ys
(C x xs) ++ ys = C x (xs ++ ys)
