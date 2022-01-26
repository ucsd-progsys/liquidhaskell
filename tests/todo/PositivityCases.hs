{-@ LIQUID "--no-positivity-check" @-}
{-# LANGUAGE GADTs #-}
module Positivity where 

{-
Occurrence            | Coq | LH  | unsound* 
------------------------------------------------
Strictly Positive     | OK  | OK  | No
Negative              | Err | Err | Yes
Guarded Negative      | Err | Err | Hopefully no
Non Strictly Positive | Err | OK  | Yes in Coq unclear for LH


Note, Coq also has Nested Positivity: https://coq.inria.fr/refman/language/core/inductive.html#nested-positivity

*unsound here means there is an example that generates false (bot). 

Things are clear for strictly positive and negative. 

For the guarded negative we need 
an example that proves false or a proof that they are OK (consistent). 

Non strictly positive one can derive bot in Coq:  
   https://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/ 
It is unclear if this ports to LH. 
This check is currently not implemented since it will reject many examples. 
Maybe have an option? 
-}


data StrictlyPositive where  
      StrictlyPositive    :: Int -> StrictlyPositive -> StrictlyPositive 
data Negative where  
      Negative            :: Int -> (Negative -> Bot) -> Negative 
data GuardedNegative where  
      GuardedNegative     :: Int -> (GuardedNegative -> Bot) -> GuardedNegative 
data NonStrictlyPositive where  
      NonStrictlyPositive :: Int -> ((NonStrictlyPositive -> Int) -> Bot) -> NonStrictlyPositive 

{-@ data StrictlyPositive where 
      StrictlyPositive    :: n:Int -> Prop (Occ n)                   -> Prop (Occ n) @-}

{-@ data Negative where 
      Negative            :: n:Int -> (Prop (Occ n) -> Bot)          -> Prop (Occ n) @-}

{-@ data GuardedNegative where 
      GuardedNegative     :: n:Int -> (Prop (Occ {n-1}) -> Bot)      -> Prop (Occ n) @-}

{-@ data NonStrictlyPositive where 
      NonStrictlyPositive :: n:Int -> ((Prop (Occ n) -> Int) -> Bot) -> Prop (Occ n) @-}
data Occ = Occ Int

{-

Inductive positivity: nat -> Prop :=
  | strictlyPositive: forall n, positivity n -> positivity n 
  (* all three below are rejected as non strictly positive *)
  | negative: forall n, (positivity n -> nat) -> positivity n
  | guardedNegative: forall n, (positivity (n - 1) -> nat) -> positivity n 
  | nonStrictlyPositive: forall n, ((nat -> positivity n) -> nat) -> positivity n.

-}

{-@ measure prop :: a -> b @-}
{-@ type Prop E = { p:_ | prop p = E } @-}
{-@ type Bot = {v:() | false } @-}
type Bot = () 

-- Example that generates bot using the Negative definition   

contra :: Int -> Negative -> Bot
{-@ contra :: n:Int -> Prop (Occ n) -> Bot @-}
contra n evidence = case evidence of 
  Negative            _ f -> f evidence 


{-@ evidence :: n:Int -> Prop (Occ n) @-}
evidence :: Int -> Negative 
evidence n = Negative n (contra n) 


{-@ bot :: Bot @-}
bot :: Bot
bot = contra 42 (evidence 42)
