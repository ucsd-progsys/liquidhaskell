{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--diff"        @-}
{- LIQUID "--short-names" @-}
{-@ infixr ++              @-}  -- TODO: Silly to have to rewrite this annotation!
{-@ infixr <~              @-}  -- TODO: Silly to have to rewrite this annotation!

--------------------------------------------------------------------------------
-- | Inspired by 
--     http://flint.cs.yale.edu/cs428/coq/sf/Hoare.html
--     http://flint.cs.yale.edu/cs428/coq/sf/Hoare2.html
--------------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}

module Axiomatic where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import           Expressions  
import           Imp 
import           BigStep hiding (And)

--------------------------------------------------------------------------------
{- | A Floyd-Hoare triple is of the form 

        { P }  c { Q }

     where 
      
     - `P` and `Q` are assertions (think `BExp`) and 
     - `c` is a command (think `Com`) 
    
     A Floyd-Hoare triple states that 

     IF 

     * The program `c` is starts at a state where the *precondition* `P` is True, and 
     * The program finishes execution

     THEN 

     * At the final state, the *postcondition* `Q` will also evaluate to True.

     -}

{- | Lets paraphrase the following Hoare triples in English.

   1) {True}   c {X = 5}

   2) {X = m}  c {X = m + 5}

   3) {X <= Y} c {Y <= X}

   4) {True}   c {False}

-}


--------------------------------------------------------------------------------
-- | The type `Assertion` formalizes the type for the 
--   assertions (i.e. pre- and post-conditions) `P`, `Q`
--   appearing in the triples {P} c {Q}

type Assertion = BExp 

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
{- | Legitimate Triples 
--------------------------------------------------------------------------------

Which of the following triples are "legit" i.e.,  the claimed relation between 
`pre`condition` `P`, `com`mand `C`, and `post`condition `Q` is true?

   1) {True}  
        X <~ 5 
      {X = 5}

   2) {X = 2} 
        X <~ X + 1 
      {X = 3}

   3) {True}  
        X <~ 5; 
        Y <~ 0 
      {X = 5}

   4) {True}  
        X <~ 5; 
        Y <~ X 
      {Y = 5}

   5) {X = 2 && X = 3} 
        X <~ 5 
      {X = 0}

   6) {True} 
        SKIP 
      {False}

   7) {False} 
        SKIP 
      {True}

   8) {True} 
        WHILE True DO 
          SKIP 
      {False}

   9) {X = 0}
        WHILE X <= 0 DO 
          X <~ X + 1 
      {X = 1}

   10) {X = 1}
         WHILE not (X <= 0) DO 
           X <~ X + 1 
       {X = 100}
 -}

--------------------------------------------------------------------------------
-- | `Legit` formalizes the notion of when a Floyd-Hoare triple is legitimate 
--------------------------------------------------------------------------------
{-@ type Legit P C Q =  s:{State | bval P s} 
                     -> s':_ -> Prop (BStep C s s') 
                     -> {bval Q s'} 
  @-}
type Legit = State -> State -> BStep -> Proof 

-- | {True}  X <~ 5  {X = 5} ---------------------------------------------------

{-@ leg1 :: Legit tt (Assign {"x"} (N 5)) (Equal (V {"x"}) (N 5)) @-}
leg1 :: Legit  
leg1 s s' (BAssign {}) 
  = S.lemma_get_set "x" 5 s 


-- | {True}  X <~ 5; y <- X  {X = 5} -------------------------------------------

{-@ leg3 :: Legit tt (Seq (Assign {"x"} (N 5)) (Assign {"y"} (V {"x"}))) (Equal (V {"y"}) (N 5)) @-}
leg3 :: Legit  
leg3 s s' (BSeq _ _ _ smid _ (BAssign {}) (BAssign {})) 
  = S.lemma_get_set "x" 5 s &&& S.lemma_get_set "y" 5 smid 


-- | {False}  X <~ 5  {X = 0} --------------------------------------------------

{-@ leg5 :: Legit ff (Assign {"x"} (N 5)) (Equal (V {"x"}) (N 22)) @-}
leg5 :: Legit  
leg5 s s' _ = () 


--------------------------------------------------------------------------------
-- | Two simple facts about Floyd-Hoare Triples --------------------------------
--------------------------------------------------------------------------------

{-@ lem_post_true :: p:_ -> c:_ -> Legit p c tt @-}
lem_post_true :: Assertion -> Com -> Legit
lem_post_true p c = \s s' c_s_s' -> () 

{-@ lem_pre_false :: c:_ -> q:_ -> Legit ff c q @-}
lem_pre_false :: Com -> Assertion -> Legit 
lem_pre_false c q = \s s' c_s_s' -> () 


-- | Assignment 

--  { Y = 1     }  X <~ Y      { X = 1 }

--  { X + Y = 1 }  X <~ X + Y  { X = 1 }

--  { a = 1     }  X <~ a      { X = 1 }


{- | Lets fill in the blanks

     { ??? } 
        x <~ 3 
     { x == 3 }

     { ??? } 
        x <~ x + 1 
     { x <= 5 }

     { ??? }
        x <~ y + 1 
     { 0 <= x && x <= 5 }

 -} 


{- | To conclude that an arbitrary postcondition `Q` holds after 
     `x <~ a`, we need to assume that Q holds before `x <~ a` 
     but with all occurrences of `x` replaced by `a` in `Q` 

     Lets revisit the example above:

     { ??? } 
        x <~ 3 
     { x == 3 }

     { ??? } 
        x <~ x + 1 
     { x <= 5 }

     { ??? }
        x <~ y + 1 
     { 0 <= x && x <= 5 }

  -} 

--------------------------------------------------------------------------------
-- | `Valid`ity of an assertion
--------------------------------------------------------------------------------


-- forall s. bval P s == True 
{-@ type Valid P = s:State -> { v: Proof | bval P s } @-}
type Valid = State -> Proof 

-- x >= 0 || x < 0

{-@ checkValid :: p:_ -> Valid p -> () @-}
checkValid :: Assertion -> Valid -> ()
checkValid p v = () 

-- x <= 0 
ex0 = checkValid (e0 `bImp` e1) (\_ -> ())
  where 
    e0 = (V "x") `Leq` (N 0)
    e1 = ((V "x") `Minus` (N 1)) `Leq` (N 0)

-- x <= 0 => x - 1 <= 0
-- e1 = e0 `bImp` ((V "x" `Minus` N 1) `Leq` (N 0))

--------------------------------------------------------------------------------
-- | When does an assertion `Imply` another
--------------------------------------------------------------------------------

{-@ type Imply P Q = Valid (bImp P Q) @-}

-- 10 <= x => 5 <= x
{-@ v1 :: _ -> Imply (Leq (N 10) (V {"x"})) (Leq (N 5) (V {"x"})) @-} 
v1 :: a -> Valid 
v1 _ = \_ -> ()

-- (0 < x && 0 < y) ===> (0 < x + y)
{-@ v2 :: _ -> Imply (bAnd (Leq (N 0) (V {"x"})) (Leq (N 0) (V {"y"}))) 
                     (Leq (N 0) (Plus (V {"x"}) (V {"y"})))
  @-}             
v2 :: a -> Valid 
v2 _ = \_ -> ()

--------------------------------------------------------------------------------
-- | The Floyd-Hoare proof system
--------------------------------------------------------------------------------

data FHP where 
  FH :: Assertion -> Com -> Assertion -> FHP

data FH where 
  FHSkip    :: Assertion -> FH 
  FHAssign  :: Assertion -> Vname -> AExp -> FH 
  FHSeq     :: Assertion -> Com -> Assertion -> Com -> Assertion -> FH -> FH -> FH 
  FHIf      :: Assertion -> Assertion -> BExp -> Com -> Com -> FH -> FH -> FH
  FHWhile   :: Assertion -> BExp -> Com -> FH -> FH 
  FHConPre  :: Assertion -> Assertion -> Assertion -> Com -> Valid -> FH -> FH 
  FHConPost :: Assertion -> Assertion -> Assertion -> Com -> FH -> Valid -> FH 

{-@ data FH where 
      FHSkip   :: p:_
               -> Prop (FH p Skip p) 
    | FHAssign :: q:_ -> x:_ -> a:_
               -> Prop (FH (bsubst x a q) (Assign x a) q) 
    | FHSeq    :: p:_ -> c1:_ -> q:_ -> c2:_ -> r:_ 
               -> Prop (FH p c1 q) 
               -> Prop (FH q c2 r) 
               -> Prop (FH p (Seq c1 c2) r) 
    | FHIf     :: p:_ -> q:_ -> b:_ -> c1:_ -> c2:_
               -> Prop (FH (bAnd p b)       c1 q) 
               -> Prop (FH (bAnd p (Not b)) c2 q)
               -> Prop (FH p (If b c1 c2) q)
    | FHWhile  :: inv:_ -> b:_ -> c:_
               -> Prop (FH (bAnd inv b) c inv) 
               -> Prop (FH inv (While b c) (bAnd inv (Not b)))
    | FHConPre :: p':_ -> p:_ -> q:_ -> c:_  
               -> Imply p' p
               -> Prop (FH p c q) 
               -> Prop (FH p' c q)
    | FHConPost :: p:_ -> q:_ -> q':_ -> c:_  
                -> Prop (FH p c q) 
                -> Imply q q'
                -> Prop (FH p c q')
  @-}

--------------------------------------------------------------------------------
-- | THEOREM: Soundness of Floyd-Hoare Logic 
--------------------------------------------------------------------------------
-- thm_fh_legit :: p:_ -> c:_ -> q:_ -> Prop (FH p c q) -> Legit p c q

-- thm_legit_fh :: p:_ -> c:_ -> q:_ -> Legit p c q -> Prop (FH p c q) 


--------------------------------------------------------------------------------
-- | Making FH Algorithmic: Verification Conditions 
--------------------------------------------------------------------------------
data ICom 
  = ISkip                          -- skip 
  | IAssign Vname     AExp         -- x := a
  | ISeq    ICom      ICom         -- c1; c2
  | IIf     BExp      ICom  ICom   -- if b then c1 else c2
  | IWhile  Assertion BExp  ICom   -- while {I} b c 
  deriving (Show)

{-@ reflect pre @-}
pre :: ICom -> Assertion -> Assertion 
pre ISkip          q = q
pre (IAssign x a)  q = bsubst x a q 
pre (ISeq c1 c2)   q = pre c1 (pre c2 q)
pre (IIf b c1 c2)  q = bIte b (pre c1 q) (pre c2 q) 
pre (IWhile i _ _) _ = i 




{-@ reflect vc @-}
vc :: ICom -> Assertion -> Assertion
vc ISkip          _ = tt 
vc (IAssign {})   _ = tt 
vc (ISeq c1 c2)   q = (vc c1 (pre c2 q)) `bAnd` (vc c2 q)
vc (IIf _ c1 c2)  q = (vc c1 q) `bAnd` (vc c2 q)
vc (IWhile i b c) q = ((bAnd i b)       `bImp` (pre c i)) `bAnd`   -- { i && b} c { i }
                      ((bAnd i (Not b)) `bImp` q        ) `bAnd`   -- { i & ~b} => Q 
                      vc c i

{-@ reflect erase @-}
erase :: ICom -> Com 
erase ISkip          = Skip 
erase (IAssign x a)  = Assign x a 
erase (ISeq c1 c2)   = Seq (erase c1) (erase c2)
erase (IIf b c1 c2)  = If b (erase c1) (erase c2)
erase (IWhile _ b c) = While b (erase c)

-----------------------------------------------------------------------------------
-- | THEOREM: Soundness of VC
-----------------------------------------------------------------------------------
-- thm_vc :: c:_ -> q:_ -> Valid (vc c q) -> Legit (pre c q) (erase c) q

-----------------------------------------------------------------------------------
-- | Extending the above to triples [HW] 
-----------------------------------------------------------------------------------

{-@ reflect vc' @-}
vc' :: Assertion -> ICom -> Assertion -> Assertion 
vc' p c q = bAnd (bImp p (pre c q)) (vc c q) 

-----------------------------------------------------------------------------------
-- | THEOREM: Soundness of VC'
-----------------------------------------------------------------------------------
-- thm_vc' :: p:_ -> c:_ -> q:_ -> Valid (vc' p c q) -> Legit p (erase c) q


