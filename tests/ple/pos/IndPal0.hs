{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module IndPal0 where

import Prelude hiding ((++))
import Language.Haskell.Liquid.ProofCombinators

{-@ infixr ++  @-}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a] 
[]     ++ ys = ys 
(x:xs) ++ ys = x : (xs ++ ys)

{-@ reflect rev @-}
rev :: [a] -> [a] 
rev []     = [] 
rev (x:xs) = rev xs ++ [x] 

{-@ reflect mkPal @-}
mkPal :: a -> [a] -> [a]
mkPal x xs = x : (xs ++ [x])

{-@ reflect single @-}
single :: a -> [a]
single x = [x]

--------------------------------------------------------------------------------
-- | The Prop declaring the Palindrome predicate 
data PalP a where
  Pal :: [a] -> PalP a

-- | The Predicate implementing the Palindrom predicate 
data Pal a where
  Pal0 :: Pal a 
  Pal1 :: a -> Pal a 
  Pals :: a -> [a] -> Pal a -> Pal a 

{-@ data Pal a where
        Pal0 :: Prop (Pal []) 
        Pal1 :: x:_ -> Prop (Pal (single x)) 
        Pals :: x:_ -> xs:_ -> Prop (Pal xs) -> Prop (Pal (mkPal x xs)) 
  @-}

{-@ assume admit :: _ -> { false } @-}
admit () = ()

{-@ ple lemma_pal @-}
{-@ lemma_pal :: xs:_ -> p:Prop (Pal xs) -> { xs = rev xs } @-}
lemma_pal :: [a] -> Pal a -> Proof
lemma_pal []  Pal0           = () 
lemma_pal [_] (Pal1 _)       = () 
lemma_pal xs (Pals y ys pys) = admit ()




