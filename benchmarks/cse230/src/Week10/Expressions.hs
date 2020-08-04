{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}

{-# LANGUAGE PartialTypeSignatures #-}

module Expressions where

import qualified State as S 
import ProofCombinators 

--------------------------------------------------------------------------------
-- | Arithmetic Expressions 
--------------------------------------------------------------------------------
type Vname = String

data AExp  
  = N Val 
  | V Vname 
  | Plus  AExp AExp 
  | Minus AExp AExp 
  | Times AExp AExp 
  deriving (Show)

type Val   = Int 
type State = S.GState Vname Val 

{-@ reflect aval @-}
aval                :: AExp -> State -> Val 
aval (N n) _         = n 
aval (V x) s         = S.get s x 
aval (Plus  e1 e2) s = aval e1 s + aval e2 s
aval (Minus e1 e2) s = aval e1 s - aval e2 s
aval (Times e1 e2) s = aval e1 s * aval e2 s

{-@ reflect asgn @-}
asgn :: Vname -> AExp -> State -> State
asgn x a s = S.set s x (aval a s)

{-@ reflect subst @-}
subst :: Vname -> AExp -> AExp -> AExp
subst x e (Plus  a1 a2)  = Plus  (subst x e a1) (subst x e a2)
subst x e (Minus a1 a2)  = Minus (subst x e a1) (subst x e a2)
subst x e (Times a1 a2)  = Times (subst x e a1) (subst x e a2)
subst x e (V y) | x == y = e
subst _ _ a              = a

{-@ lem_subst :: x:_ -> a:_ -> e:_ -> s:_ -> 
      { aval (subst x a e) s = aval e (asgn x a s) } 
  @-}
lem_subst :: Vname -> AExp -> AExp -> State -> Proof
lem_subst x a (V y) s
  | x == y                    = ()
  | otherwise                 = S.lemma_get_not_set y x (aval a s) s
lem_subst x a (N i) s         = ()
lem_subst x a (Plus  e1 e2) s = lem_subst x a e1 s &&& lem_subst x a e2 s
lem_subst x a (Minus e1 e2) s = lem_subst x a e1 s &&& lem_subst x a e2 s
lem_subst x a (Times e1 e2) s = lem_subst x a e1 s &&& lem_subst x a e2 s



--------------------------------------------------------------------------------
-- | Boolean Expressions 
--------------------------------------------------------------------------------

data BExp 
  = Bc    Bool       -- true, false 
  | Not   BExp       -- not b 
  | And   BExp BExp  -- b1 && b2
  | Leq   AExp AExp  -- a1 <= a2 
  | Equal AExp AExp  -- a1 == a2 
  deriving (Show)

{-@ reflect .&&. @-}
(.&&.) :: BExp -> BExp -> BExp 
b1 .&&. b2 = And b1 b2 

{-@ reflect .=>. @-}
(.=>.) :: BExp -> BExp -> BExp 
b1 .=>. b2 = bImp b1 b2 

{-@ reflect bAnd @-}
bAnd :: BExp -> BExp -> BExp 
bAnd b1 b2 = And b1 b2 

{-@ reflect bIte @-}
bIte :: BExp -> BExp -> BExp -> BExp 
bIte p b1 b2 = And (bImp p b1) (bImp (Not p) b2)

{-@ reflect .==. @-}
(.==.) :: AExp -> AExp -> BExp 
b1 .==. b2 = Equal b1 b2 

{-@ reflect .<=. @-}
(.<=.) :: AExp -> AExp -> BExp 
b1 .<=. b2 = Leq b1 b2 

{-@ reflect bOr @-}
bOr :: BExp -> BExp -> BExp 
bOr b1 b2 = Not ((Not b1) `And` (Not b2))
       
{-@ reflect bImp @-}
bImp :: BExp -> BExp -> BExp 
bImp b1 b2 = bOr (Not b1) b2

{-@ reflect bLess @-}
bLess :: AExp -> AExp -> BExp 
bLess a1 a2 = And (Leq a1 a2) (Not (Equal a1 a2))

{-@ reflect tt @-}
tt :: BExp 
tt = Bc True 

{-@ reflect ff @-}
ff :: BExp 
ff = Bc False 

{-@ reflect bval @-}
bval :: BExp -> State -> Bool
bval (Bc   b)      _ = b 
bval (Not  b)      s = not (bval b s) 
bval (And  b1 b2)  s = bval b1 s && bval b2 s 
bval (Leq  a1 a2)  s = aval a1 s <= aval a2 s 
bval (Equal a1 a2) s = aval a1 s == aval a2 s 


{-@ reflect bsubst @-}
bsubst :: Vname -> AExp -> BExp -> BExp
bsubst x a (Bc    b)     = Bc    b
bsubst x a (Not   b)     = Not   (bsubst x a b)
bsubst x a (And   b1 b2) = And   (bsubst x a b1) (bsubst x a b2)
bsubst x a (Leq   a1 a2) = Leq   (subst  x a a1) (subst  x a a2)
bsubst x a (Equal a1 a2) = Equal (subst  x a a1) (subst  x a a2)

{-@ lem_bsubst :: x:_ -> a:_ -> b:_ -> s:_ -> 
      { bval (bsubst x a b) s = bval b (asgn x a s) } 
  @-}
lem_bsubst :: Vname -> AExp -> BExp -> State -> Proof 
lem_bsubst x a (Bc _) _        = () 
lem_bsubst x a (Not b)       s = lem_bsubst x a b  s 
lem_bsubst x a (And b1 b2)   s = lem_bsubst x a b1 s &&& lem_bsubst x a b2 s 
lem_bsubst x a (Leq a1 a2)   s = lem_subst  x a a1 s &&& lem_subst  x a a2 s 
lem_bsubst x a (Equal a1 a2) s = lem_subst  x a a1 s &&& lem_subst  x a a2 s 

