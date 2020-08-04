{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module BigStep where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import           Expressions hiding (And)
import           Imp 

{- 
  BStep c s1 s2 

  ------------------[BSkip]
    BStep Skip s s


    s' = set x (aval a s) s
  ----------------------------------[BAssign]
    BStep (x := a) s s'


    BStep c1 s smid    BStep c2 smid s'
  ----------------------------------------[BSeq]
    BStep (c1; c2) s s' 


    bval b s1 = TRUE      BStep c1 s s'
  ----------------------------------------
    BStep (If b c1 c2) s s' 

    bval b s = FALSE     BStep c2 s s'
  -------------------------------
    BStep (If b c1 c2) s s' 

    WHILE 
 -}

--------------------------------------------------------------------------------
-- | Big-step Semantics 
--------------------------------------------------------------------------------

data BStepP where
  BStep :: Com -> State -> State -> BStepP 

data BStep where 
  BSkip   :: State -> BStep 
  BAssign :: Vname -> AExp -> State -> BStep 
  BSeq    :: Com   -> Com  -> State  -> State -> State -> BStep -> BStep -> BStep 
  BIfT    :: BExp  -> Com  -> Com   -> State -> State -> BStep -> BStep  
  BIfF    :: BExp  -> Com  -> Com   -> State -> State -> BStep -> BStep
  BWhileF :: BExp  -> Com  -> State -> BStep 
  BWhileT :: BExp  -> Com  -> State -> State -> State -> BStep -> BStep -> BStep 

{-@ data BStep  where 
      BSkip   :: s:State 
              -> Prop (BStep Skip s s)
    | BAssign :: x:Vname -> a:AExp -> s:State 
              -> Prop (BStep (Assign x a) s (asgn x a s)) 
    | BSeq    :: c1:Com -> c2:Com -> s1:State -> s2:State -> s3:State 
              -> Prop (BStep c1 s1 s2) -> Prop (BStep c2 s2 s3) 
              -> Prop (BStep (Seq c1 c2) s1 s3)
    | BIfT    :: b:BExp -> c1:Com -> c2:Com -> s:{State | bval b s} -> s1:State
              -> Prop (BStep c1 s s1) -> Prop (BStep (If b c1 c2) s s1)
    | BIfF    :: b:BExp -> c1:Com -> c2:Com -> s:{State | not (bval b s)} -> s2:State
              -> Prop (BStep c2 s s2) -> Prop (BStep (If b c1 c2) s s2)
    | BWhileF :: b:BExp -> c:Com -> s:{State | not (bval b s)} 
              -> Prop (BStep (While b c) s s)
    | BWhileT :: b:BExp -> c:Com -> s1:{State | bval b s1} -> s1':State -> s2:State
              -> Prop (BStep c s1 s1') -> Prop (BStep (While b c) s1' s2)
              -> Prop (BStep (While b c) s1 s2)
  @-}  


{-@ reflect cmd_1 @-}
cmd_1 = "x" <~ N 5

{-@ reflect cmd_2 @-}
cmd_2 = "y" <~ (V "x")

{-@ reflect cmd_1_2 @-}
cmd_1_2 = cmd_1 @@ cmd_2

{-@ reflect prop_set @-}
prop_set cmd x v s = BStep cmd s (S.set s x v)

{-@ step_1 :: s:State -> Prop (prop_set cmd_1 {"x"} 5 s)  @-}
step_1 s =  BAssign "x" (N 5) s

{-@ step_2 :: s:{State | S.get s "x" == 5} -> Prop (prop_set cmd_2 {"y"} 5 s) @-}
step_2 s = BAssign "y" (V "x") s

{-@ step_1_2 :: s:State -> Prop (BStep cmd_1_2 s (S.set (S.set s {"x"} 5) {"y"} 5)) @-}
step_1_2 s = BSeq cmd_1 cmd_2 s s1 s2 (step_1 s) (step_2 s1)
  where
    s1     = S.set s  "x" 5
    s2     = S.set s1 "y" 5



-------------------------------------------------------------------------------
-- | We say `Sim c1 c2` or `c1` is simulated by `c2` if 
--   the transitions of `c1` are contained within those of `c2`
-------------------------------------------------------------------------------

{-@ type Sim C1 C2 = s:State -> t:State -> Prop (BStep C1 s t) -> Prop (BStep C2 s t) @-}
type SimT = State -> State -> BStep -> BStep 


---------------------------------------------------------------------------------
-- | IMP is Deterministic
---------------------------------------------------------------------------------

{- 
{-@ thm_bigstep_det 
      :: s:_ -> t1:_ -> t2:_ -> c:_
      -> Prop (BStep c s t1) 
      -> Prop (BStep c s t2) 
      -> { t1 == t2 }
  @-}
thm_bigstep_det :: State -> State -> State -> Com -> BStep -> BStep -> Proof




{- -}
thm_bigstep_det s t t' Skip         (BSkip {})   (BSkip {})
    = ()
  
thm_bigstep_det s t t' (Assign x a) (BAssign {}) (BAssign {})
    = ()
  
thm_bigstep_det s t t' (Seq c1 c2)  (BSeq _ _ _ s1 s2 s_s1 s1_s2) (BSeq _ _ _ s1' s2' s_s1' s1_s2')
    = thm_bigstep_det s1_eq_s1' s2 s2' c2 s1_s2 s1_s2'        
    where s1_eq_s1' = s1 ? thm_bigstep_det s  s1 s1' c1 s_s1  s_s1'
  
thm_bigstep_det s t t' (If b c1 c2) (BIfT _ _ _ _ _t c1_s_t) (BIfT _ _ _ _ _t' c1_s_t')
    = thm_bigstep_det s t t' c1 c1_s_t c1_s_t'
  
thm_bigstep_det s t t' (If b c1 c2) (BIfF _ _ _ _ _t c2_s_t) (BIfF _ _ _ _ _t' c2_s_t')
    = thm_bigstep_det s t t' c2 c2_s_t c2_s_t'
  
thm_bigstep_det s t t' (While b c)  (BWhileF {}) (BWhileF {})
    = ()
  
thm_bigstep_det s t t' (While b c)  (BWhileT _ _ _ s1 _ s_s1 s1_t) (BWhileT _ _ _ s1' _ s_s1' s1_t')
    = thm_bigstep_det s1_eq_s1' t t' (While b c) s1_t s1_t'   
    where s1_eq_s1' = s1 ? thm_bigstep_det s s1 s1' c s_s1 s_s1'

thm_bigstep_det _ _ _ _  _ _ 
    = impossible "no really" 
  
-}
