{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module RosePLEDiv where

type Vname = String

{-@ data Pred [psize] @-}

data Pred
  = Var Vname           -- ^ x, y, z    variables
  | Not Pred            -- ^ ~ p        negation
  | Or  Pred Pred       -- ^ p1 \/ p2   disjunction
  | And Pred Pred       -- ^ p1 /\ p2   conjunction
  deriving (Show)

{-@ measure psize @-}
{-@ psize :: Pred -> Nat @-}
psize :: Pred -> Int
psize (Var _)   = 0
psize (Not p)   = 1 + psize p
psize (Or p q)  = 1 + mmax (psize p) (psize q)
psize (And p q) = 1 + mmax (psize p) (psize q)

{-@ inline mmax @-}
mmax :: Int -> Int -> Int
mmax x y = if x > y then x else y

{-@ type NNF = {v:Pred | isNNF v} @-}

{-@ measure isNNF @-}
isNNF :: Pred -> Bool
isNNF (Var _)   = True
isNNF (And p q) = isNNF p && isNNF q
isNNF (Or  p q) = isNNF p && isNNF q
isNNF (Not p)   = isVar p

{-@ measure isVar @-}
isVar :: Pred -> Bool
isVar (Var _) = True
isVar _       = False

{- MUTUALLY-REC version #1 -}

{-@ reflect nnf @-}
{-@ nnf :: Pred -> NNF @-}
nnf :: Pred -> Pred
nnf (Var x)   = Var x
nnf (And p q) = Or (neg p) (neg q)
nnf (Or p q)  = And (neg p) (neg q)
nnf (Not p)   = neg p

{-@ reflect neg @-}
{-@ neg :: Pred -> NNF @-}
neg :: Pred -> Pred
neg (Var x)   = Not (Var x)
neg (And p q) = Or (nnf p) (nnf q)
neg (Or p q)  = And (nnf p) (nnf q)
neg (Not p)   = nnf p


{- SINGLE function version #2 -}

{-@ reflect crunch @-}
{-@ crunch :: Pred -> NNF @-}
crunch :: Pred -> Pred
crunch (And p q)       = And (crunch p) (crunch q)
crunch (Or p q)        = Or (crunch p) (crunch q)
crunch (Not (And p q)) = And (crunch (Not p)) (crunch (Not q))
crunch (Not (Or p q))  = Or (crunch (Not p)) (crunch (Not q))
crunch (Not (Not p))   = crunch p
crunch p               = p

