{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--ple" @-}

-- Beware that trivial changes to this file would cause verification
-- to fail at some time. Renaming the module to Rest would be one of those
-- changes.
module Rest where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (length, max)

-- | The type of a Stitch expression
data Ty = TInt
        | TBool
        | TFun { funArgTy :: Ty, funResTy :: Ty }
  deriving (Show, Eq)

{-@
data Ty = TInt
        | TBool
        | TFun { funArgTy :: Ty, funResTy :: Ty }
@-}

{-@ measure isFunTy @-}
isFunTy :: Ty -> Bool
isFunTy (TFun _ _) = True
isFunTy _ = False


-- | An @ArithOp ty@ is an operator on numbers that produces a result
-- of type @ty@
data ArithOp
  = Plus
  | Minus
  | Times
  | Divide
  | Mod
  | Less
  | LessE
  | Greater
  | GreaterE
  | Equals
  deriving (Eq, Show)

-- | Extract the result type of an Op
{-@ measure arithType @-}
arithType :: ArithOp -> Ty
arithType Plus     = TInt
arithType Minus    = TInt
arithType Times    = TInt
arithType Divide   = TInt
arithType Mod      = TInt
arithType Less     = TBool
arithType LessE    = TBool
arithType Greater  = TBool
arithType GreaterE = TBool
arithType Equals   = TBool

{-@ invariant { op:ArithOp | arithType op = TBool || arithType op = TInt } @-}


{-@ type Nat = { v : Int | v >= 0 } @-}
type Nat = Int

{-@ inline max @-}
max :: Ord a => a -> a -> a
max a b = if a > b then a else b

{-@ inline minus @-}
minus :: Nat -> Nat -> Nat
minus a b = max 0 (a - b)

data List a = Cons { head :: a, tail :: List a } | Nil

{-@
reflect elemAt
elemAt :: n : Nat -> { xs : List a | length xs > n } -> a
@-}
elemAt :: Nat -> List a -> a
elemAt 0 (Cons x _) = x
elemAt i (Cons _ xs) = elemAt (i-1) xs

{-@
measure length
length :: xs : List a -> Nat
@-}
length :: List a -> Nat
length Nil = 0
length (Cons _ xs) = 1 + length xs

{-@
reflect append
append ::
  xs : List a ->
  ys : List a ->
  { zs : List a | length zs == length xs + length ys }
 @-}
append :: List a -> List a -> List a
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

{-@
appendLengh
  :: xs : List a
  -> ys : List a
  -> { length (append xs ys) == length xs + length ys}
@-}
appendLengh :: List a -> List a -> Proof
appendLengh xs ys = trivial ? append xs ys

{-@
elemAtThroughAppend
  :: i : Nat
  -> xs : { xs : List a | i < length xs }
  -> ys : List a
  -> { elemAt i (append xs ys) = elemAt i xs }
@-}
elemAtThroughAppend :: Nat -> List a -> List a -> Proof
elemAtThroughAppend i xs ys =
  if i == 0 then trivial
  else case xs of
    Cons _ xss -> elemAtThroughAppend (i - 1) xss ys
    Nil -> trivial


{-@
predicate WellTyped E CTX = checkBindings CTX E && numFreeVarsExp E <= length CTX
type WellTypedExp CTX = { e : Exp | WellTyped e CTX }
type FunExp = { e : Exp | isFunTy (exprType e) }
type ExpT T = { e : Exp | T = exprType e }
data Exp
  = Var Ty Nat
  | Lam Ty Exp
  | App (e1 :: FunExp) (ExpT (funArgTy (exprType e1)))
  | Let Exp Exp
  | Arith (ExpT TInt) ArithOp (ExpT TInt)
  | Cond (ExpT TBool) (a :: Exp) (ExpT (exprType a))
  | Fix ({ e:FunExp | funArgTy (exprType e) = funResTy (exprType e) })
  | IntE Int
  | BoolE Bool
@-}

-- | Checked expression
data Exp
  = Var Ty Nat
  | Lam Ty Exp
  | App Exp Exp
  | Let Exp Exp
  | Arith Exp ArithOp Exp
  | Cond Exp Exp Exp
  | Fix Exp
  | IntE Int
  | BoolE Bool
  deriving Show

{-@ measure exprType @-}
exprType :: Exp -> Ty
exprType (Var ty _) = ty
exprType (Lam ty e) = TFun ty (exprType e)
exprType (App e1 _) = funResTy (exprType e1)
exprType (Let _ e2) = exprType e2
exprType (Arith _ op _) = arithType op
exprType (Cond _ e2 _) = exprType e2
exprType (Fix e) = funResTy (exprType e)
exprType (IntE _) = TInt
exprType (BoolE _) = TBool

-- | Check that all occurrences of a variable have the given type
{-@
reflect checkBindings
checkBindings
  :: ctx : List Ty
  -> { e : Exp | numFreeVarsExp e <= length ctx }
  -> Bool
@-}
checkBindings :: List Ty -> Exp -> Bool
checkBindings ctx (Var vty i) = elemAt i ctx == vty
checkBindings ctx (Lam t e) = checkBindings (Cons t ctx) e
checkBindings ctx (App e1 e2) = checkBindings ctx e1 && checkBindings ctx e2
checkBindings ctx (Let e1 e2) = checkBindings ctx e1 && checkBindings (Cons (exprType e1) ctx) e2
checkBindings ctx (Arith e1 _ e2) = checkBindings ctx e1 && checkBindings ctx e2
checkBindings ctx (Cond e1 e2 e3) = checkBindings ctx e1 && checkBindings ctx e2 && checkBindings ctx e3
checkBindings ctx (Fix e) = checkBindings ctx e
checkBindings _ (IntE _) = True
checkBindings _ (BoolE _) = True

{-@
rewriteWith aClosedExpIsValidInAnyContext [appendLengh]
aClosedExpIsValidInAnyContext
  :: ctx0 : List Ty
  -> ctx1 : List Ty
  -> e : Exp
  -> { WellTyped e ctx0 <=>
       WellTyped e (append ctx0 ctx1) && numFreeVarsExp e <= length ctx0
     }
@-}
aClosedExpIsValidInAnyContext :: List Ty -> List Ty -> Exp -> Proof
aClosedExpIsValidInAnyContext ctx0 ctx1 e = case e of
  Var _ i ->
    if i < length ctx0 then elemAtThroughAppend i ctx0 ctx1
    else trivial
  Lam ty body ->
    aClosedExpIsValidInAnyContext (Cons ty ctx0) ctx1 body
  App e1 e2 ->
    aClosedExpIsValidInAnyContext ctx0 ctx1 e1 ? aClosedExpIsValidInAnyContext ctx0 ctx1 e2
  Let e1 e2 ->
    aClosedExpIsValidInAnyContext ctx0 ctx1 e1 ? aClosedExpIsValidInAnyContext (Cons (exprType e1) ctx0) ctx1 e2
  Arith e1 _ e2 ->
    aClosedExpIsValidInAnyContext ctx0 ctx1 e1 ? aClosedExpIsValidInAnyContext ctx0 ctx1 e2
  Cond e1 e2 e3 ->
    aClosedExpIsValidInAnyContext ctx0 ctx1 e1
      ? aClosedExpIsValidInAnyContext ctx0 ctx1 e2
      ? aClosedExpIsValidInAnyContext ctx0 ctx1 e3
  Fix body ->
    aClosedExpIsValidInAnyContext ctx0 ctx1 body
  IntE _ -> trivial
  BoolE _ -> trivial

{-@
measure numFreeVarsExp
numFreeVarsExp :: Exp -> Nat
@-}
numFreeVarsExp :: Exp -> Nat
numFreeVarsExp (Var _ v) = v + 1
numFreeVarsExp (Lam _ body) = minus (numFreeVarsExp body) 1
numFreeVarsExp (App e1 e2) = max (numFreeVarsExp e1) (numFreeVarsExp e2)
numFreeVarsExp (Let e1 e2) =
    max (numFreeVarsExp e1) (minus (numFreeVarsExp e2) 1)
numFreeVarsExp (Arith e1 _ e2) = max (numFreeVarsExp e1) (numFreeVarsExp e2)
numFreeVarsExp (Cond e1 e2 e3) =
    max (max (numFreeVarsExp e1) (numFreeVarsExp e2)) (numFreeVarsExp e3)
numFreeVarsExp (Fix body) = numFreeVarsExp body
numFreeVarsExp (IntE _) = 0
numFreeVarsExp (BoolE _) = 0


