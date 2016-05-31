-- | Unification for simple terms a la Zombie
-- | cite : http://www.seas.upenn.edu/~sweirich/papers/congruence-extended.pdf

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

module Unify where

import Proves
import qualified  Data.Set as S


-- | Data Types
data Term = TBot | TVar Int | TFun Term Term
  deriving (Eq)
{-@ data Term [tsize] @-}

type Substitution = L (P Int Term)
data P a b = P a b


-- | Unification
-- | If unification succeds then the returned substitution makes input terms equal
-- | Unification may fail with Nothing, or diverge

{-@ Lazy unify @-}
{-@ unify :: t1:Term -> t2:Term
          -> Maybe {θ:Substitution | apply θ t1 == apply θ t2 } @-}
unify :: Term -> Term -> Maybe Substitution
unify TBot TBot
  = Just Emp
unify t1@(TVar i) t2
  | not (S.member i (freeVars t2))
  = Just $ C (P i t2) Emp `byTheorem` theoremVar t2 i
unify t1 t2@(TVar i)
  | not (S.member i (freeVars t1))
  = Just $ C (P i t1) Emp `byTheorem` theoremVar t1 i
unify (TFun t11 t12) (TFun t21 t22)
  = case unify t11 t21 of
      Just θ1 -> case unify (apply θ1 t12) (apply θ1 t22) of
                   Just θ2 -> Just $ append θ2 θ1 `byTheorem` theoremFun t11 t12 t21 t22 θ1 θ2
                   Nothing -> Nothing
      _       -> Nothing
unify t1 t2
  = Nothing


-- | Helper Functions

{-@ measure freeVars @-}
freeVars :: Term -> S.Set Int
freeVars TBot = S.empty
freeVars (TFun t1 t2) = S.union (freeVars t1) (freeVars t2)
freeVars (TVar i)     = S.singleton i


{-@ axiomatize apply @-}
apply :: Substitution -> Term -> Term
apply s t
  | llen s == 0
  = t
  | otherwise
  = applyOne (hd s) (apply (tl s) t)

{-@ axiomatize applyOne @-}
applyOne :: (P Int Term) -> Term -> Term
applyOne su t
  | isTVar t, fromTVar t == myfst su
  = mysnd su
  | isTFun t
  = TFun (applyOne su (tfunArg t)) (applyOne su (tfunRes t))
  | otherwise
  = t


-- | Proving the required theorems
theoremFun :: Term -> Term -> Term -> Term -> Substitution -> Substitution -> Proof
{-@ theoremFun
  :: t11:Term
  -> t12:Term
  -> t21:Term
  -> t22:Term
  -> θ1:{Substitution | apply θ1 t11 == apply θ1 t21 }
  -> θ2:{Substitution | apply θ2 (apply θ1 t12) == apply θ2 (apply θ1 t22) }
  -> { apply (append θ2 θ1) (TFun t11 t12) ==
       apply (append θ2 θ1) (TFun t21 t22)  }
  @-}
theoremFun t11 t12 t21 t22 θ1 θ2
  =   apply (append θ2 θ1) (TFun t11 t12)
  ==! TFun (apply (append θ2 θ1) t11) (apply (append θ2 θ1) t12)
      ? split_fun t11 t12 (append θ2 θ1)
  ==! TFun (apply θ2 (apply θ1 t11))  (apply (append θ2 θ1) t12)
      ? append_apply θ2 θ1 t11
  ==! TFun (apply θ2 (apply θ1 t21))  (apply θ2 (apply θ1 t12))
      ? append_apply θ2 θ1 t12
  ==! TFun (apply θ2 (apply θ1 t21))  (apply θ2 (apply θ1 t22))
  ==! TFun (apply (append θ2 θ1) t21) (apply θ2 (apply θ1 t22))
      ? append_apply θ2 θ1 t21
  ==! TFun (apply (append θ2 θ1) t21) (apply (append θ2 θ1) t22)
      ? append_apply θ2 θ1 t22
  ==! TFun (apply (append θ2 θ1) t21) (apply (append θ2 θ1) t22)
      ? split_fun t21 t22 (append θ2 θ1)
  ==! apply (append θ2 θ1) (TFun t21 t22)
  *** QED

split_fun :: Term -> Term -> Substitution -> Proof
{-@ split_fun :: t1:Term -> t2:Term -> θ:Substitution
   -> {apply θ (TFun t1 t2) == TFun (apply θ t1) (apply θ t2)} / [llen θ] @-}
split_fun t1 t2 Emp
  =   apply Emp (TFun t1 t2)
  ==! TFun t1 t2
  ==! TFun (apply Emp t1) (apply Emp t2)
  *** QED
split_fun t1 t2 (C su θ)
    =   apply (C su θ) (TFun t1 t2)
    ==! applyOne su (apply θ (TFun t1 t2))
    ==! applyOne su (TFun (apply θ t1) (apply θ t2))
        ? split_fun t1 t2 θ
    ==! TFun (applyOne su (apply θ t1)) (applyOne su (apply θ t2))
    ==! TFun (apply (C su θ) t1) (apply (C su θ) t2)
    *** QED

append_apply :: Substitution -> Substitution -> Term -> Proof
{-@ append_apply
   :: θ1:Substitution
   -> θ2:Substitution
   -> t :Term
   -> {apply θ1 (apply θ2 t) == apply (append θ1 θ2) t}
  @-}
append_apply Emp θ2 t
  =   apply Emp (apply θ2 t)
  ==! apply θ2 t
  ==! apply (append Emp θ2) t
  *** QED
append_apply (C su θ) θ2 t
  =   apply (C su θ) (apply θ2 t)
  ==! applyOne su (apply θ (apply θ2 t))
  ==! applyOne su (apply (append θ θ2) t)
       ? append_apply θ θ2 t
  ==! apply (C su (append θ θ2)) t
  ==! apply (append (C su θ) θ2) t
  *** QED


{-@ theoremVar :: t:Term
             -> i:{Int | not (S.member i (freeVars t)) }
             -> {apply (C (P i t) Emp) (TVar i) == apply (C (P i t) Emp) t } @-}
theoremVar :: Term -> Int ->Proof
theoremVar t i
  =   apply (C (P i t) Emp) (TVar i)
  ==! applyOne (P i t) (apply Emp (TVar i))
  ==! applyOne (P i t) (TVar i)
  ==! t
  ==! applyOne (P i t) t
       ? theoremVarOne t i t
  ==! applyOne (P i t) (apply Emp t)
  ==! apply (C (P i t) Emp) t
  *** QED

{-@ theoremVarOne :: t:Term
             -> i:{Int | not (S.member i (freeVars t)) }
             -> ti:Term
             -> { t == applyOne (P i ti) t } @-}
theoremVarOne :: Term -> Int -> Term -> Proof
theoremVarOne (TFun t1 t2) i ti
  =   applyOne (P i ti) (TFun t1 t2)
  ==! TFun (applyOne (P i ti) t1) (applyOne (P i ti) t2)
  ==! TFun t1 (applyOne (P i ti) t2)
      ? theoremVarOne t1 i ti
  ==! TFun t1 t2
      ? theoremVarOne t2 i ti
  *** QED
theoremVarOne t i ti
  =   applyOne (P i ti) t
  ==! t
  *** QED



-- | Helpers to lift Terms and Lists into logic...
-- | With some engineering all these can be automated...
-- | Lifting Terms into logic
{-@ measure tsize @-}
tsize :: Term -> Int
{-@ invariant {t:Term | tsize t >= 0 } @-}

-- NV TODO: something goes wrong with measure invariants
{-@ tsize :: Term -> Int  @-}
tsize TBot     = 0
tsize (TVar _) = 0
tsize (TFun t1 t2) = 1 + (tsize t1) + (tsize t2)

{-@ measure isTBot @-}
{-@ measure isTVar @-}
{-@ measure isTFun @-}

isTBot, isTVar, isTFun :: Term -> Bool
isTBot TBot = True
isTBot _    = False

isTVar (TVar _) = True
isTVar _        = False

isTFun (TFun _ _) = True
isTFun _          = False

{-@ measure tfunArg @-}
{-@ measure tfunRes @-}
tfunArg, tfunRes :: Term -> Term
{-@ tfunArg, tfunRes :: t:{Term | isTFun t} -> {v:Term | tsize v < tsize t} @-}
tfunArg (TFun t _) = t
tfunRes (TFun _ t) = t

{-@ measure fromTVar @-}
{-@ fromTVar :: {t:Term | isTVar t} -> Int @-}
fromTVar :: Term -> Int
fromTVar (TVar i) = i


{-@ measure myfst @-}
{-@ measure mysnd @-}
myfst :: (P a b) -> a
myfst (P x _) = x
mysnd :: (P a b) -> b
mysnd (P _ x) = x


-- | List Helpers
{-@ axiomatize append @-}
append :: L a -> L a -> L a
append xs ys
  | llen xs == 0 = ys
  | otherwise    = C (hd xs) (append (tl xs) ys)

data L a = Emp | C a (L a)
{-@ data L [llen] @-}

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen Emp      = 0
llen (C _ xs) = 1 + llen xs

{-@ measure hd @-}
{-@ hd :: {v:L a | llen v > 0 } -> a @-}
hd :: L a -> a
hd (C x _) = x

{-@ measure tl @-}
{-@ tl :: xs:{L a | llen xs > 0 } -> {v:L a | llen v == llen xs - 1 } @-}
tl :: L a -> L a
tl (C _ xs) = xs
