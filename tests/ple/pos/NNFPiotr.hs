{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

module NNFPiotr where

import Prelude hiding (lookup)

data Wff = Var Int
         | Not Wff
         | Wff :|: Wff
         | Wff :&: Wff
         deriving (Eq, Ord)

data NNF = Atom Bool Int
         | NOr NNF NNF
         | NAnd NNF NNF

{-@ reflect toWff @-}
toWff :: NNF -> Wff
toWff (Atom True i) = Var i
toWff (Atom False i) = Not (Var i)
toWff (NOr f g) = toWff f :|: toWff g
toWff (NAnd f g) = toWff f :&: toWff g

{-@ reflect lookup @-}
lookup :: [a] -> a -> Int -> a
lookup []     def _ = def
lookup (v:_)  _   0 = v
lookup (_:vs) def k = lookup vs def (k-1)

{-@ reflect eval @-}
eval :: [Bool] -> Wff -> Bool
eval s (Var i) = lookup s False i
eval s (f :&: g) = eval s f && eval s g
eval s (f :|: g) = (eval s f) || (eval s g)
eval s (Not f) = not (eval s f)

{-@ reflect evalNNF @-}
evalNNF :: [Bool] -> NNF -> Bool
evalNNF s (Atom True i)  = lookup s False i
evalNNF s (Atom False i) = not (lookup s False i)
evalNNF s (NOr p q)      = evalNNF s p || evalNNF s q
evalNNF s (NAnd p q)     = evalNNF s p && evalNNF s q

{-@ toNNF :: s:[Bool] -> p:Wff -> { q: NNF | eval s p = evalNNF s q } @-}
toNNF :: [Bool] -> Wff -> NNF
toNNF _ (Var i)         = Atom True i
toNNF s (p :|: q)       = (toNNF s p) `NOr`  (toNNF s q)
toNNF s (p :&: q)       = (toNNF s p) `NAnd` (toNNF s q)
toNNF s (Not p)         = case p of
                            Not p -> toNNF s p
                            Var i -> Atom False i
                            p :|: q -> toNNF s (Not p :&: Not q)
                            p :&: q -> toNNF s (Not p :|: Not q)
