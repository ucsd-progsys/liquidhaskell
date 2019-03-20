
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
--

{-@ LIQUID "--reflection" @-}

module Language.Haskell.Liquid.RTick.Combinators where 
  (

  -- Basic:
    Proof         -- Simply the unit type.
  , QED(..)       -- 'ASS': Signify the end of an /unfinished/ proof.
                  -- 'QED': Signify the end of a /complete/ proof.
  , (&&&)         -- Combine proofs.
  , (***)         -- Discard final result at the end of a proof.
  , (?)           -- Appeal to an external theorem.
  , isAss         -- Check whether a proof is complete.
  , toProof       -- Cast to proof.
  , trivial       -- Trivial proof.
  , withTheorem   -- Appeal to an external theorem.
  -- Equational:
  , (==.)         -- Equality.
  , (==?)         -- Equality (assumption).
  , eq            -- Equality. Note: 'eq' is inlined in the logic.
  -- Inequational:
  , (<.)          -- Less than.
  , (<?)          -- Less than (assumption).
  , (<=.)         -- Less than or equal.
  , (<=?)         -- Less than or equal (assumption).
  , (>.)          -- Greater than.
  , (>?)          -- Greater than (assumption).
  , (>=.)         -- Greater than or equal.
  , (>=?)         -- Greater than or equal (assumption).
  , (<=>.)        -- Cost equivalence.
  , (<=>?)        -- Cost equivalence (assumption)
  , (>~>.)        -- Improvement.
  , (>~>?)        -- Improvement (assumption).
  , (.>==)        -- Quantified improvement.
  , (?>==)        -- Quantified improvement (assumption).
  , (<~<.)        -- Diminishment.
  , (<~<?)        -- Diminishment (assumption).
  , (.<==)        -- Quantified diminishment.
  , (?<==)        -- Quantified diminishment (assumption).
  -- Cost separators:
  , (==>.)        -- Quantified improvement.
  , (==>?)        -- Quantified improvement (assumption).
  , (==<.)        -- Quantified diminishment.
  , (==<?)        -- Quantified diminishment (assumption).
  , (==!)
  , assert
  ) where

import RTick ( Tick(..) )

--
-- Proof combinators for extrinsic cost analysis.
--

-------------------------------------------------------------------------------
-- | Basic:
-------------------------------------------------------------------------------

{-@ assert :: b:{Bool | b} -> {b} @-}
assert :: Bool -> Proof
assert _ = ()

-- unchecked
(==!) :: a -> a -> a
_ ==! x = x


type Proof = ()
data QED   = QED | ASS

{-@ toProof :: a -> Proof @-}
toProof :: a -> Proof
toProof _ = ()
{-# INLINE toProof #-}

{-@ trivial :: Proof @-}
trivial :: Proof
trivial = ()
{-# INLINE trivial #-}

{-@ measure isAss @-}
isAss :: QED -> Bool
isAss ASS = True
isAss QED = False

{-@ assume (***) :: a -> qed:QED -> { if (isAss qed) then false else true } @-}
infixl 1 ***
(***) :: a -> QED -> Proof
_ *** _ = ()
{-# INLINE (***) #-}

{-@ (?) :: x:a -> Proof -> { v:a | x == v } @-}
infixl 3 ?
(?) :: a -> Proof -> a
x ? _ = x
{-# INLINE (?) #-}

{-@ (&&&) :: Proof -> Proof -> Proof @-}
infixl 3 &&&
(&&&) :: Proof -> Proof -> Proof
x &&& _ = x
{-# INLINE (&&&) #-}

{-@ withTheorem :: x:a -> Proof -> { v:a | x == v } @-}
withTheorem :: a -> Proof -> a
withTheorem x _ = x
{-# INLINE withTheorem #-}

-------------------------------------------------------------------------------
-- | Equational:
-------------------------------------------------------------------------------

--
-- Equality.
--
{-@ (==.) :: x:a -> { y:a | x == y } -> { v:a | x == v && y == v } @-}
infixl 3 ==.
(==.) :: a -> a -> a
_ ==. x = x
{-# INLINE (==.) #-}

{-@ assume (==?) :: x:a -> y:a -> { v:a | x == v && y == v } @-}
infixl 3 ==?
(==?) :: a -> a -> a
_ ==? x = x
{-# INLINE (==?) #-}

--
-- Equality. Note: 'eq' is inlined in the logic, so can be used in
-- reflected functions.
--
{-@ eq :: x:a -> { y:a | x == y } -> { v:a | x == v && y == v } @-}
eq :: a -> a -> a
_ `eq` x = x
{-# INLINE eq #-}

-------------------------------------------------------------------------------
-- | Inequational:
-------------------------------------------------------------------------------

--
-- Less than.
--
{-@ (<.) :: m:a -> { n:a | m < n } -> { o:a | o == n } @-}
infixl 3 <.
(<.) :: a -> a -> a
_ <. n = n
{-# INLINE (<.) #-}

{-@ assume (<?) :: m:a -> n:a -> { o:a | o == n && m < n } @-}
infixl 3 <?
(<?) :: a -> a -> a
_ <? n = n
{-# INLINE (<?) #-}

--
-- Less than or equal.
--
{-@ (<=.) :: m:a -> { n:a | m <= n } -> { o:a | o == n } @-}
infixl 3 <=.
(<=.) :: a -> a -> a
_ <=. n = n
{-# INLINE (<=.) #-}

{-@ assume (<=?) :: m:a -> n:a -> { o:a | o == n && m <= n } @-}
infixl 3 <=?
(<=?) :: a -> a -> a
_ <=? n = n
{-# INLINE (<=?) #-}

--
-- Greater than.
--
{-@ (>.) :: m:a -> { n:a | m > n } -> { o:a | o == n } @-}
infixl 3 >.
(>.) :: a -> a -> a
_ >. y = y
{-# INLINE (>.) #-}

{-@ assume (>?) :: m:a -> n:a -> { o:a | o == n && m > n } @-}
infixl 3 >?
(>?) :: a -> a -> a
_ >? y = y
{-# INLINE (>?) #-}

--
-- Greater than or equal.
--
{-@ (>=.) :: m:a -> { n:a | m >= n } -> { o:a | o == n } @-}
infixl 3 >=.
(>=.) :: a -> a -> a
_ >=. n = n
{-# INLINE (>=.) #-}

{-@ assume (>=?) :: m:a -> n:a -> { o:a | o == n && m >= n } @-}
infixl 3 >=?
(>=?) :: a -> a -> a
_ >=? n = n
{-# INLINE (>=?) #-}

--
-- Cost equivalence.
--
{-@ predicate COSTEQ T1 T2 = tval T1 == tval T2 && tcost T1 == tcost T2 @-}

{-@ (<=>.)
  :: t1:Tick a
  -> { t2:Tick a | COSTEQ t1 t2 }
  -> { t3:Tick a | COSTEQ t1 t2 && COSTEQ t1 t3 && COSTEQ t2 t3 }
@-}
infixl 3 <=>.
(<=>.) :: Tick a -> Tick a -> Tick a
(<=>.) _ t2 = t2
{-# INLINE (<=>.) #-}

{-@ assume (<=>?)
  :: t1:Tick a -> t2:Tick a
  -> { t3:Tick a | COSTEQ t1 t2 && COSTEQ t1 t3 && t2 == t3 }
@-}
infixl 3 <=>?
(<=>?) :: Tick a -> Tick a -> Tick a
(<=>?) _ t2 = t2
{-# INLINE (<=>?) #-}

--
-- Improvement.
--
{-@ predicate IMP T1 T2 = tval T1 == tval T2 && tcost T1 >= tcost T2 @-}

{-@ (>~>.)
  :: t1:Tick a
  -> { t2:Tick a | IMP t1 t2 }
  -> { t3:Tick a | IMP t1 t2 && IMP t1 t3 && t2 == t3 }
@-}
infixl 3 >~>.
(>~>.) :: Tick a -> Tick a -> Tick a
(>~>.) _ t2 = t2
{-# INLINE (>~>.) #-}

{-@ assume (>~>?)
  :: t1:Tick a -> t2:Tick a
  -> { t3:Tick a | IMP t1 t2 && IMP t1 t3 && t2 == t3 }
@-}
infixl 3 >~>?
(>~>?) :: Tick a -> Tick a -> Tick a
(>~>?) _ t2 = t2
{-# INLINE (>~>?) #-}

--
-- Quantified improvement.
--
{-@ predicate QIMP T1 N T2 = tval T1 == tval T2 && tcost T1 == tcost T2 + N @-}

{-@ (.>==)
  :: t1:Tick a
  -> n:Int
  -> { t2:Tick a | QIMP t1 n t2 }
  -> { t3:Tick a | QIMP t1 n t2 && QIMP t1 n t3 && t2 == t3 }
@-}
infixl 3 .>==
(.>==) :: Tick a -> Int -> Tick a -> Tick a
(.>==) _ _ t2 = t2
{-# INLINE (.>==) #-}

{-@ assume (?>==)
  :: t1:Tick a -> n:Nat -> t2:Tick a
  -> { t3:Tick a | QIMP t1 n t2 && QIMP t1 n t3 && t2 == t3 }
@-}
infixl 3 ?>==
(?>==) :: Tick a -> Int -> Tick a -> Tick a
(?>==) _ _ t2 = t2
{-# INLINE (?>==) #-}

--
-- Diminishment.
--
{-@ predicate DIM T1 T2 = tval T1 == tval T2 && tcost T1 <= tcost T2 @-}

{-@ (<~<.)
  :: t1:Tick a
  -> { t2:Tick a | DIM t1 t2 }
  -> { t3:Tick a | DIM t1 t2 && DIM t1 t3 && t2 == t3 }
@-}
infixl 3 <~<.
(<~<.) :: Tick a -> Tick a -> Tick a
(<~<.) _ t2 = t2
{-# INLINE (<~<.) #-}

{-@ assume (<~<?)
  :: t1:Tick a -> t2:Tick a
  -> { t3:Tick a | DIM t1 t2 && DIM t1 t3 && t2 == t3 }
@-}
infixl 3 <~<?
(<~<?) :: Tick a -> Tick a -> Tick a
(<~<?) _ t2 = t2
{-# INLINE (<~<?) #-}

--
-- Quantified diminishment.
--
{-@ predicate QDIM T1 N T2 = tval T1 == tval T2 && tcost T1 + N == tcost T2 @-}

{-@ (.<==)
  :: t1:Tick a
  -> n:Nat
  -> { t2:Tick a | QDIM t1 n t2 }
  -> { t3:Tick a | QDIM t1 n t2 && QDIM t1 n t3 && t2 == t3 }
@-}
infixl 3 .<==
(.<==) :: Tick a -> Int -> Tick a -> Tick a
(.<==) _ _ t2 = t2
{-# INLINE (.<==) #-}

{-@ assume (?<==)
  :: t1:Tick a -> n:Nat -> t2:Tick a
  -> { t3:Tick a | QDIM t1 n t2 && QDIM t1 n t3 && t2 == t3 }
@-}
infixl 3 ?<==
(?<==) :: Tick a -> Int -> Tick a -> Tick a
(?<==) _ _ t2 = t2
{-# INLINE (?<==) #-}

-------------------------------------------------------------------------------
-- | Cost separators:
-------------------------------------------------------------------------------

--
-- Quantified improvement.
--
{-@ (==>.) :: (a -> b) -> a -> b @-}
infixl 3 ==>.
(==>.) :: (a -> b) -> a -> b
f ==>. a = f a
{-# INLINE (==>.) #-}

--
-- Quantified improvement (assumption).
--
{-@ (==>?) :: (a -> b) -> a -> b @-}
infixl 3 ==>?
(==>?) :: (a -> b) -> a -> b
f ==>? a = f a
{-# INLINE (==>?) #-}

--
-- Quantified diminishment.
--
{-@ (==<.) :: (a -> b) -> a -> b @-}
infixl 3 ==<.
(==<.) :: (a -> b) -> a -> b
f ==<. a = f a
{-# INLINE (==<.) #-}

--
-- Quantified diminishment (assumption).
--
{-@ (==<?) :: (a -> b) -> a -> b @-}
infixl 3 ==<?
(==<?) :: (a -> b) -> a -> b
f ==<? a = f a
{-# INLINE (==<?) #-}
