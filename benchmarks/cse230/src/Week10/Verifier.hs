{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--diff"        @-}

module Verifier () where 

import           ProofCombinators
import qualified State as S
import           Expressions  
import           Imp 
import           BigStep hiding (And)
import           Axiomatic 

imports = (FH undefined undefined undefined)

----------------------------------------------------------------
-- TODO: Move into FloydHoare.hs 
----------------------------------------------------------------

----------------------------------------------------------------
-- | Lets build a 'verify'-er
----------------------------------------------------------------

{-@ verify :: p:_ -> c:_ -> q:_ -> Valid (vc' p c q) -> () @-}
verify :: Assertion -> ICom -> Assertion -> Valid -> () 
verify _ _ _ _ = () 

----------------------------------------------------------------
ex1   :: () -> ()
ex1 _ = verify p c q (\_ -> ()) 
  where 
    p = tt                                    -- { true } 
    c = IAssign "x" (N 5)                     --    x := 5
    q = Equal (V "x") (N 5)                   -- { x == 5 }

----------------------------------------------------------------

ex2   :: () -> () 
ex2 _ = verify p c q (\_ -> ()) 
  where 
    p = Equal (V "x") (N 2)                   -- { x = 2 } 
    c = IAssign "x" (Plus (V "x") (N 1))      --    x := x + 1
    q = Equal (V "x") (N 3)                   -- { x = 3 }

----------------------------------------------------------------

ex2a   :: () -> () 
ex2a _ = verify p c q (\_ -> ()) 
  where 
    p  = Equal (V "x") (N 2)                   -- { x = 2 } 
    c  = c1 `ISeq` c1                          --    x := x + 1 
    c1 = IAssign "x" (Plus (V "x") (N 1))      --    x := x + 1
    q  = Equal (V "x") (N 4)                   -- { x = 4 }

----------------------------------------------------------------

ex4  :: () -> () 
ex4 _  = verify p (c1 `ISeq` c2) q (\_ -> ()) 
  where 
    p  = tt                                    -- { True } 
    c1 = IAssign "x" (N 5)                     --    x := 5 
    c2 = IAssign "y" (V "x")                   --    y := x 
    q  = Equal (V "y") (N 5)                   -- { y = 5 }

----------------------------------------------------------------
ex5  :: () -> () 
ex5 _ = verify p c q (\_ -> ()) 
  where 
    p = ((V "x") `Equal` (N 2)) `bAnd` 
        ((V "x") `Equal` (N 3))                -- { x = 2 && x = 3} 
    c = IAssign "x" (N 5)                      --    x := 5
    q = V "x" `Equal` N 0                      -- { x = 0}

----------------------------------------------------------------

ex8  :: () -> () 
ex8 _ = verify p c q (\_ -> ()) 
  where 
    p = tt                                     -- { true } 
    c = IWhile i tt ISkip                      --    WHILE_i true SKIP 
    q = ff                                     -- { false }
    i = tt -- undefined -- TODO: In class

----------------------------------------------------------------

ex9  :: () -> () 
ex9 _ = verify p c q (\_ -> ()) 
  where 
    p = Equal (V "x") (N 0)                    -- { x = 0 } 
    c = IWhile i (Leq (V "x") (N 0))           --   WHILE_i (x <= 0) DO
          (IAssign "x" (Plus (V "x") (N 1)))   --     x := x + 1
    q = Equal (V "x") (N 1)                    -- { x = 1 } 
    i = undefined -- TODO: In class

----------------------------------------------------------------
ex10  :: () -> () 
ex10 _ = verify p c q (\_ -> ()) 
  where 
    p = Equal (V "x") (N 1)                    -- { x = 1 } 
    c = IWhile i (Not (Leq (V "x") (N 0)))     --   WHILE_i not (x <= 0) DO
          (IAssign "x" (Plus (V "x") (N 1)))   --     x := x + 1
    q = Equal (V "x") (N 100)                  -- { x = 100 } 
    i = undefined -- TODO: In class

-------------------------------------------------------------------------------
-- | Example 1: branching
-------------------------------------------------------------------------------

bx1 :: () -> () 
bx1 _ = verify p c q (\_ -> ()) 
  where 
    p = tt                                     -- { true } 
    c = IIf (Equal (V "x") (N 0))              --   IF x == 0 
            (IAssign "y" (N 2))                --     THEN y := 2
            (IAssign "y" (Plus (V "x") (N 1))) --     ELSE y := x + 1
    q = Leq (V "x") (V "y")                    -- { x <= y } 

-------------------------------------------------------------------------------
-- | Example 2: Swapping Using Addition and Subtraction 
-------------------------------------------------------------------------------

bx2 :: () -> () 
bx2 _ = verify p c q (\_ -> ()) 
  where 
    p =      (V "x" `Equal` V "a") 
      `bAnd` (V "y" `Equal` V "b")                -- { x = a && y = b } 
    c =      IAssign "x" (Plus  (V "x") (V "y"))  --     x := x + y
      `ISeq` IAssign "y" (Minus (V "x") (V "y"))  --     y := x - y
      `ISeq` IAssign "x" (Minus (V "x") (V "y"))  --     x := x - y
    q =      (V "x" `Equal` V "b")                -- { x = a && y = b } 
      `bAnd` (V "y" `Equal` V "a") 


-------------------------------------------------------------------------------
-- | Example 4: Reduce to Zero  
-------------------------------------------------------------------------------

bx4 :: () -> () 
bx4 _ = verify p c q (\_ -> ()) 
  where 
    p = tt                                      -- { true } 
    c = IWhile i (Not (Equal (V "x") (N 0)))    --   WHILE not (x == 0) DO: 
          (IAssign "x" (Minus (V "x") (N 1)))   --     x := x - 1
    q = (V "x" `Equal` N 0)                     -- { x = 0 } 
    i = tt 




