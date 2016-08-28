{-@ LIQUID "--total" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

-- From: https://github.com/jstolarek/sandbox/blob/master/agda/agda-curious

module StackMachine where

import Prelude hiding (max)

type Val   = Int
data Expr  = EVal Val | EAdd Expr Expr
data Instr = Push Val | Add

eval :: Expr -> Val
eval (EVal v)     = v
eval (EAdd e1 e2) = eval e1 + eval e2

compile :: Expr -> [Instr]
compile (EVal v)     = [Push v]
compile (EAdd e1 e2) = compile e1 ++ compile e2 ++ [Add]

{-@ run :: is:[Instr] -> {v:[Val] | len v >= needs is} -> [Val] @-}
run :: [Instr] -> [Val] -> [Val]
run (Add    : is) (v1:v2:vs) = run is ((v1 + v2) : vs)
run (Push v : is) vs         = run is (    v     : vs)
run []            vs         = vs
run (Add    : _ ) _          = die "impossible"

{-@ die :: {v:String | false} -> a @-}
die :: String -> a
die = error

{-@ measure needs @-}
needs :: [Instr] -> Int
needs (i:is) = max (pops i) ((needs is) - (pushes i))
needs []     = 0

{-@ measure pops @-}
pops :: Instr -> Int
pops Add      = 2
pops (Push _) = 0

{-@ measure pushes @-}
pushes :: Instr -> Int
pushes Add      = (-1)
pushes (Push _) = 1

{-@ inline max @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y

{-
needs []
  = 0
needs [Add]
  = max 2 (0 + 1)
  = 2
needs [Add, Add]
  = max 2 (2 + 1)
  = 3
needs [Add, Add, Add]
  = max 2 (3 + 1)
  = 4

needs [Add, Add , Add] = 4
needs [Add , Add]      = 3
needs [Add]            = 2
needs [Push v]         = 0

[1, 2, 3, 4]

needs [                              add ]
  = 2

needs [                      push 4, add ]
  = max 0 (2 - 1)
  = 1

needs [                 add, push 4, add ]
  = max 2 (1 + 1)
  = 2

needs [         push 3, add, push 4, add ]
  = max 0 (2 - 1)
  = 1

needs [ push 2, push 3, add, push 4, add ]
  = max 0 (1 - 1)
  = 0
-}
