{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE IncoherentInstances   #-}

module Language.Haskell.Liquid.ProofCombinators (

  -- ATTENTION! `Admit` and `(==!)` are UNSAFE: they should not belong the final proof term

  -- * Proof is just a () alias
  Proof
  , toProof 

  -- * Proof constructors
  , trivial, unreachable, (***), QED(..)

  -- * Proof certificate constructors
  , (?)

  -- * These two operators check all intermediate equalities
  , (===) -- proof of equality is implicit eg. x === y
  , (=<=) -- proof of equality is implicit eg. x <= y
  , (=>=)  -- proof of equality is implicit eg. x =>= y 

  -- * This operator does not check intermediate equalities
  , (==.) 

  -- Uncheck operator used only for proof debugging
  , (==!) -- x ==! y always succeeds

  -- * Combining Proofs
  , (&&&)
  , withProof 
  , impossible 


) where

-------------------------------------------------------------------------------
-- | Proof is just a () alias -------------------------------------------------
-------------------------------------------------------------------------------

type Proof = ()

toProof :: a -> Proof
toProof _ = ()

-------------------------------------------------------------------------------
-- | Proof Construction -------------------------------------------------------
-------------------------------------------------------------------------------

-- | trivial is proof by SMT

trivial :: Proof
trivial =  ()

-- {-@ unreachable :: {v : Proof | False } @-}
unreachable :: Proof
unreachable =  ()

-- All proof terms are deleted at runtime.
{- RULE "proofs are irrelevant" forall (p :: Proof). p = () #-}

-- | proof casting
-- | `x *** QED`: x is a proof certificate* strong enough for SMT to prove your theorem
-- | `x *** Admit`: x is an unfinished proof

infixl 3 ***
{-@ assume (***) :: a -> p:QED -> { if (isAdmit p) then false else true } @-}
(***) :: a -> QED -> Proof
_ *** _ = ()

data QED = Admit | QED

{-@ measure isAdmit :: QED -> Bool @-}
{-@ Admit :: {v:QED | isAdmit v } @-}


-------------------------------------------------------------------------------
-- | * Checked Proof Certificates ---------------------------------------------
-------------------------------------------------------------------------------

-- Any (refined) carries proof certificates.
-- For example 42 :: {v:Int | v == 42} is a certificate that
-- the value 42 is equal to 42.
-- But, this certificate will not really be used to proof any fancy theorems.

-- Below we provide a number of equational operations
-- that constuct proof certificates.

-- | Implicit equality

-- x === y returns the proof certificate that
-- result value is equal to both x and y
-- when y == x (as assumed by the operator's precondition)

infixl 3 ===
{-@ (===) :: x:a -> y:{a | y == x} -> {v:a | v == x && v == y} @-}
(===) :: a -> a -> a
_ === y  = y

infixl 3 =<=
{-@ (=<=) :: x:a -> y:{a | x <= y} -> {v:a | v == y} @-}
(=<=) :: a -> a -> a
_ =<= y  = y

infixl 3 =>=
{-@ (=>=) :: x:a -> y:{a | x >= y}  -> {v:a | v == y} @-}
(=>=) :: a -> a -> a
_ =>= y  = y

-------------------------------------------------------------------------------
-- | `?` is basically Haskell's $ and is used for the right precedence
-- | `?` lets you "add" some fact into a proof term
-------------------------------------------------------------------------------

infixl 3 ?

{-@ (?) :: forall a b <pa :: a -> Bool, pb :: b -> Bool>. a<pa> -> b<pb> -> a<pa> @-}
(?) :: a -> b -> a 
x ? _ = x 
{-# INLINE (?)   #-} 

-------------------------------------------------------------------------------
-- | Assumed equality
-- 	`x ==! y `
--   returns the admitted proof certificate that result value is equals x and y
-------------------------------------------------------------------------------

infixl 3 ==!
{-@ assume (==!) :: x:a -> y:a -> {v:a | v == x && v == y} @-}
(==!) :: a -> a -> a
(==!) _ y = y


-- | To summarize:
--
-- 	- (==!) is *only* for proof debugging
--	- (===) does not require explicit proof term
-- 	- (?)   lets you insert "lemmas" as other `Proof` values

-------------------------------------------------------------------------------
-- | * Unchecked Proof Certificates -------------------------------------------
-------------------------------------------------------------------------------

-- | The above operators check each intermediate proof step.
--   The operator `==.` below accepts an optional proof term
--   argument, but does not check intermediate steps.
--   TODO: What is it USEFUL FOR?

infixl 3 ==.

{-# DEPRECATED (==.) "Use (===) instead" #-}

{-# INLINE (==.) #-} 
(==.) :: a -> a -> a 
_ ==. x = x 

-------------------------------------------------------------------------------
-- | * Combining Proof Certificates -------------------------------------------
-------------------------------------------------------------------------------

(&&&) :: Proof -> Proof -> Proof
x &&& _ = x


{-@ withProof :: x:a -> b -> {v:a | v = x} @-}
withProof :: a -> b -> a
withProof x _ = x

{-@ impossible :: {v:a | false} -> b @-}
impossible :: a -> b
impossible _ = undefined

-------------------------------------------------------------------------------
-- | Convenient Syntax for Inductive Propositions 
-------------------------------------------------------------------------------

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}



