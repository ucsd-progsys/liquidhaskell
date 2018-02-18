{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--ple"            @-} 
{-@ LIQUID "--no-totality"    @-} 

module Compiler where

import Language.Haskell.Liquid.ProofCombinators

-- | Expressions ---------------------------------------------------------------

{-@ data Expr [eSize] @-}
data Expr
  = Val Int
  | Add Expr Expr

{-@ measure eSize @-}
{-@ eSize :: Expr -> {v:Int | 1 <= v} @-}
eSize :: Expr -> Int
eSize (Val n)     = 1
eSize (Add e1 e2) = 1 + eSize e1 + eSize e2

{-@ invariant {v:Expr | 1 <= eSize v } @-}

-- | Interpreter ---------------------------------------------------------------

{-@ reflect interp @-}
interp :: Expr -> Int
interp (Val n)     = n
interp (Add e1 e2) = interp e1 + interp e2

-- | Code ----------------------------------------------------------------------

{-@ data Code [cSize] @-}
data Code
  = HALT
  | PUSH Int Code
  | ADD      Code

{-@ measure cSize @-}
{-@ cSize :: Code -> Nat @-}
cSize :: Code -> Int
cSize HALT       = 0
cSize (PUSH n c) = 1 + cSize c
cSize (ADD    c) = 1 + cSize c

-- | Stack ---------------------------------------------------------------------
data Stack
  = Emp
  | Arg Int Stack

-- | Compiler ------------------------------------------------------------------

{-@ reflect compileC @-}
compileC :: Expr -> Code -> Code
compileC (Val n) c     = PUSH n c
compileC (Add e1 e2) c = compileC e2 (compileC e1 (ADD c))

{-@ reflect compile @-}
compile :: Expr -> Code
compile e = compileC e HALT

-- | VM ------------------------------------------------------------------------

{-@ reflect run @-}
run :: Code -> Stack -> Int
run HALT       (Arg n s)         = n
run (ADD c)    (Arg n (Arg m s)) = run c (Arg (n + m) s)
run (PUSH n c) s                 = run c (Arg n       s)

{-@ reflect compileAndRun @-}
compileAndRun :: Expr -> Int
compileAndRun e = run (compileC e HALT) Emp

-- | Correctness ---------------------------------------------------------------

{-@ thmCompileC :: e:Expr -> c:Code -> s:Stack ->
      { run (compileC e c) s = run c (Arg (interp e) s) }
  @-}
thmCompileC :: Expr -> Code -> Stack -> Proof
thmCompileC (Val n)     c s =  () 
thmCompileC (Add e1 e2) c s =  thmCompileC e2 (compileC e1  (ADD c)) s
                           &&& thmCompileC e1 (ADD c) (Arg (interp e2) s)

{-@ thmCompileAndRun :: e:Expr -> { compileAndRun e == interp e } @-}
thmCompileAndRun :: Expr -> Proof
thmCompileAndRun e = thmCompileC e HALT Emp


{- thmCompileC (Add e1 e2) c s
   = [ -- run (compileC (Add e1 e2) c) s
      -- ==. run (compileC e2 (compileC e1 (ADD c))) s
      {- ? -} thmCompileC e2 (compileC e1  (ADD c)) s
      -- ==. run (compileC e1 (ADD c)) (Arg (interp e2) s)
    , {- ? -} thmCompileC e1 (ADD c) (Arg (interp e2) s)
      -- ==. run (ADD c) (Arg (interp e1) (Arg (interp e2) s))
      -- ==. run c (Arg (interp e1 + interp e2) s)
      -- ==. run c (Arg (interp (Add e1 e2)) s)
    ] *** QED
 -}







---
