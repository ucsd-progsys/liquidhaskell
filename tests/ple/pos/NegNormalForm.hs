{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module NegNormalForm where

import Language.Haskell.Liquid.ProofCombinators (pleUnfold)
import Prelude hiding (not, lookup)

-------------------------------------------------------------------------------
-- | General datatype for Predicates 
-------------------------------------------------------------------------------

data Pred 
  = Var Int
  | Not Pred 
  | Or  Pred Pred 
  | And Pred Pred

{-@ data Pred [predSize] @-}

{-@ measure predSize @-}
{-@ predSize :: Pred -> Nat @-}
predSize :: Pred -> Int
predSize (Var _) = 1
predSize (Not p) = 1 + predSize p
predSize (Or p q) = 1 + predSize p + predSize q
predSize (And p q) = 1 + predSize p + predSize q

-------------------------------------------------------------------------------
-- | Define NNF as a Refinement of @Pred@ 
-------------------------------------------------------------------------------

{-@ type NNF = {v:Pred | isNNF v} @-}

{-@ measure isVar @-}
isVar :: Pred -> Bool 
isVar (Var _) = True 
isVar _       = False 

{-@ measure isNNF @-}
isNNF :: Pred -> Bool 
isNNF (Var _)   = True 
isNNF (And p q) = isNNF p && isNNF q 
isNNF (Or  p q) = isNNF p && isNNF q 
isNNF (Not p)   = isVar p 


-------------------------------------------------------------------------------
-- | Define semantics of @Pred@ 
-------------------------------------------------------------------------------

{-@ reflect lookup @-}
lookup :: [a] -> a -> Int -> a
lookup []     def _ = def
lookup (v:_)  _   0 = v 
lookup (_:vs) def k = lookup vs def (k-1) 

{-@ reflect eval @-}
eval :: [Bool] -> Pred -> Bool
eval s (Var i)   = lookup s False i
eval s (And f g) = (eval s f) && (eval s g)
eval s (Or  f g) = (eval s f) || (eval s g)
eval s (Not f)   = not (eval s f)

-------------------------------------------------------------------------------
-- | NNF Conversion with store -- "INTERNAL" VERIFICATION 
-------------------------------------------------------------------------------

{-@ reflect nnfP @-}
{-@ nnf :: s:_ -> p:_ -> {v:NNF | eval s v = eval s p} / [predSize p] @-}
nnf :: [Bool] -> Pred -> Pred 
nnf s (Var i)    = Var  i 
nnf s (Not p)    = nnf' s p  
nnf s (And p q)  = And (nnf s p) (nnf s q) 
nnf s (Or  p q)  = Or  (nnf s p) (nnf s q) 

{-@ reflect nnfN @-}
{-@ nnf' :: s:_ -> p:_ -> {v:NNF | eval s p = not (eval s v)} / [predSize p] @-}
nnf' :: [Bool] -> Pred -> Pred 
nnf' s (Var i)    = Not (Var i) 
nnf' s (Not p)    = nnf s p  
nnf' s (And p q)  = Or  (nnf' s p) (nnf' s q) 
nnf' s (Or  p q)  = And (nnf' s p) (nnf' s q) 

-------------------------------------------------------------------------------
-- | NNF Conversion 
-------------------------------------------------------------------------------

{-@ reflect nnfP @-}
{-@ nnfP :: Pred -> NNF @-} 
nnfP :: Pred -> Pred 
nnfP (Var i)    = Var i 
nnfP (Not p)    = nnfN p  
nnfP (And p q)  = And (nnfP p) (nnfP q) 
nnfP (Or  p q)  = Or  (nnfP p) (nnfP q) 

{-@ reflect nnfN @-}
{-@ nnfN :: Pred -> NNF @-} 
nnfN :: Pred -> Pred 
nnfN (Var i)    = Not (Var i) 
nnfN (Not p)    = nnfP p  
nnfN (And p q)  = Or  (nnfN p) (nnfN q) 
nnfN (Or  p q)  = And (nnfN p) (nnfN q) 

-------------------------------------------------------------------------------
-- | NNF Conversion -- "EXTERNAL" VERIFICATION 
-------------------------------------------------------------------------------

{-@ thmP :: s:_ -> p:_ -> { eval s p = eval s (nnfP p) } / [predSize p] @-}
thmP :: [Bool] -> Pred -> Bool
thmP s (Var i)   = True
thmP s (And p q) = thmP s p && thmP s q
thmP s (Or  p q) = thmP s p && thmP s q
thmP s (Not p)   = thmN s p 

{-@ thmN :: s:_  -> p:_ -> { eval s p = not (eval s (nnfN p)) } / [predSize p] @-}
thmN :: [Bool] -> Pred -> Bool
thmN s (Var i)   = True
thmN s (And p q) = thmN s p && thmN s q
thmN s (Or  p q) = thmN s p && thmN s q
thmN s (Not p)   = thmP s p 

{-@ reflect not @-}
not :: Bool -> Bool 
not b = pleUnfold (if b then False else True)
