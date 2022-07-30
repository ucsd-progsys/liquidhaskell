{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module T1371_NNF where

import Prelude hiding (lookup)

data Pred
  = Var Int
  | Not Pred
  | Or  Pred Pred
  | And Pred Pred

{-@ reflect lookup @-}
lookup :: [a] -> a -> Int -> a
lookup []     def _ = def
lookup (v:vs) def k
  | k == 0          = v
  | k <  0          = def
  | otherwise       = lookup vs def (k-1)

{-@ reflect eval @-}
eval :: [Bool] -> Pred -> Bool
eval s (Var i)   = lookup s False i
eval s (And f g) = (eval s f) && (eval s g)
eval s (Or  f g) = (eval s f) || (eval s g)
eval s (Not f)   = not (eval s f)

{-@ lazy    nnf @-}
{-@ reflect nnf @-}
nnf :: Pred -> Pred
nnf (Var i)    = (Var i)
nnf (And p q)  = And (nnf p) (nnf q)
nnf (Or  p q)  = Or  (nnf p) (nnf q)
nnf (Not f)    = nnf' f

{-@ lazy    nnf' @-}
{-@ reflect nnf' @-}
nnf' :: Pred -> Pred
nnf' (Not g)   = nnf g
nnf' (Var i)   = Not (Var i)
-- nnf' (Or  p q) = And (nnf' p) (nnf' q)                -- OK
-- nnf' (And p q) = Or  (nnf' p) (nnf' q)                -- OK
nnf' (Or  p q) = And (nnf (Not p)) (nnf (Not q))   -- PLE-DIVERGES
nnf' (And p q) = Or  (nnf (Not p)) (nnf (Not q))   -- PLE-DIVERGES

-- ODDLY, you need BOTH the PLE-DIVERGES cases to tickle the divergence...

{-@ thm :: s:[Bool] -> p:Pred -> { eval s p = eval s (nnf p) } @-}
thm :: [Bool] -> Pred -> Bool
thm s (Var i)         = True
-- thm s (And p q)       = thm s p && thm s q
-- thm s (Or  p q)       = thm s p && thm s q
-- thm s (Not p)         = undefined
thm _ _ = undefined
