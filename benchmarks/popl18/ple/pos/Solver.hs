-- | Correctness of sat solver as in Trellys
-- | http://www.seas.upenn.edu/~sweirich/papers/popl14-trellys.pdf

-- | This code is terrible.
-- | Should use cases and auto translate like in the paper's theory
-- | Also, &&, not and rest logical operators are not in scope in the axioms

{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--pruneunsorted"   @-}

module Solver where

import Data.Tuple
import Data.List (nub)
import Language.Haskell.Liquid.Prelude ((==>))
import Prelude hiding (map)

-- | Formula
type Var     = Int
data Lit     = Pos Var | Neg Var
type Clause  = L Lit
type Formula = L Clause

-- | Assignment

type Asgn = L (P Var Bool)

-- | Top-level "solver"


{-@ solve :: f:Formula -> Maybe {a:Asgn | sat a f } @-}
solve   :: Formula -> Maybe Asgn
solve f = -- find (`sat` f) (asgns f)
          find1 (satMb f) (asgns f) 
  where
	  -- satMb :: Formula -> Asgn -> Maybe Asgn 
   satMb f a = if sat a f then Just a else Nothing 

find1 :: (a -> Maybe b) -> [a] -> Maybe b 
find1 _ []     = Nothing 
find1 f (x:xs) = case f x of 
		   Just y  -> Just y 
		   Nothing -> find1 f xs 

{-@ find :: forall <p :: a -> Bool, w :: a -> Bool -> Bool>. 
            {y::a, b::{v:Bool<w y> | v} |- {v:a | v == y} <: a<p>}
            (x:a -> Bool<w x>) -> [a] -> Maybe (a<p>) @-}
find :: (a -> Bool) -> [a] -> Maybe a
find f [] = Nothing
find f (x:xs) | f x       = Just x
              | otherwise = Nothing

-- | Generate all assignments

asgns :: Formula -> [Asgn] -- generates all possible T/F vectors
asgns = go . vars
  where
  	go []     = []
  	go (x:xs) = let ass = go xs in (inject (P x True) ass) ++ (inject (P x False) ass)

  	inject x xs = (\y -> x:::y) <$> xs

vars :: Formula -> [Var]
vars = nub . toList .  go
  where
  	go Emp       = Emp
  	go (ls:::xs) = map go' ls `append` go xs

  	go' (Pos x) = x
  	go' (Neg x) = x


{-@ axiomatize sat @-}
sat :: Asgn -> Formula -> Bool
{-@ sat :: Asgn -> f:Formula -> Bool / [llen f] @-}
sat a f
  | llen f == 0
  = True
  | satClause a (hd f)
  = sat a (tl f)
  | otherwise
  = False

{-@ axiomatize satClause @-}
{-@ satClause :: Asgn -> c:Clause -> Bool / [llen c] @-}
satClause :: Asgn -> Clause -> Bool
satClause a c
  | llen c == 0
  = False
  | satLit a (hd c)
  = True
  | otherwise
  = satClause a (tl c)

{-@ axiomatize satLit @-}
satLit :: Asgn -> Lit -> Bool
satLit a l
  | isPos l   = isPosVar (fromPos l) a
  | isNeg l   = isNegVar (fromNeg l) a
  | otherwise = False

{-@ axiomatize isPosVar @-}
{-@ axiomatize isNegVar @-}
{-@ isNegVar :: Var -> a:Asgn -> Bool / [llen a] @-}
{-@ isPosVar :: Var -> a:Asgn -> Bool / [llen a] @-}
isNegVar, isPosVar :: Var -> Asgn -> Bool
isPosVar v a
  | llen a == 0
  = False
  | (myfst (hd a)) == v
  = mysndB (hd a)
  | otherwise
  = isPosVar v (tl a)


isNegVar v a
  | llen a == 0
  = False
  | (myfst (hd a)) == v
  = if mysndB (hd a) then False else True
  | otherwise
  = isNegVar v (tl a)


{-@ measure myfst @-}
myfst :: P a b -> a
myfst (P x _) = x


{-@ measure mysndB @-}
mysndB :: P a Bool -> Bool
mysndB (P _ x) = x

{-@ measure isPos @-}
isPos (Pos _) = True
isPos _       = False

{-@ measure fromPos @-}
{-@ fromPos :: {l:Lit | isPos l} -> Var @-}
fromPos :: Lit -> Var
fromPos (Pos v) = v

{-@ measure isNeg @-}
isNeg (Neg _) = True
isNeg _       = False

{-@ measure fromNeg @-}
{-@ fromNeg :: {l:Lit | isNeg l} -> Var @-}
fromNeg :: Lit -> Var
fromNeg (Neg v) = v


-- Pairs
data P a b = P a b

-- List definition
data L a = Emp | a ::: L a
{-@ data L [llen] @-}

toList Emp      = []
toList (x ::: xs) = x:toList xs

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen Emp        = 0
llen (_ ::: xs) = 1 + llen xs

{-@ measure hd @-}
{-@ hd :: {v:L a | llen v > 0 } -> a @-}
hd :: L a -> a
hd (x ::: _) = x

{-@ measure tl @-}
{-@ tl :: xs:{L a | llen xs > 0 } -> {v:L a | llen v == llen xs - 1 } @-}
tl :: L a -> L a
tl (_ ::: xs) = xs


{-@ axiomatize append @-}
append :: L a -> L a -> L a
append xs ys
  | llen xs == 0 = ys
  | otherwise    = hd xs ::: append (tl xs) ys


{-@ axiomatize map @-}
map :: (a -> b) -> L a -> L b
map f xs
    | llen xs == 0 = Emp
    | otherwise    = f (hd xs) ::: map f (tl xs)
