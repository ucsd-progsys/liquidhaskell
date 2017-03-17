{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--totality"       @-}

module ANF (Op (..), Expr (..), isImm, isAnf, anf) where

import Control.Monad.State.Lazy

mkLet :: [(Var, AnfExpr)] -> AnfExpr -> AnfExpr
imm, immExpr :: Expr -> AnfM ([(Var, AnfExpr)], ImmExpr)
anf   :: Expr -> AnfM AnfExpr
fresh :: AnfM Var

--------------------------------------------------------------------------------
-- | Types
--------------------------------------------------------------------------------
type Var = String

data Op
  = Plus
  | Minus

data Expr
  = EInt  Int
  | EVar  Var
  | ELet  Var  Expr Expr
  | EBin  Op   Expr Expr
  | ELam  Var  Expr
  | EApp  Expr Expr

--------------------------------------------------------------------------------
-- | Defining Immediate Values and ANF
--------------------------------------------------------------------------------
{-@ measure isImm @-}
isImm :: Expr -> Bool
isImm (EInt {}) = True
isImm (EVar {}) = True
isImm _         = False

-- isImm (ELet {}) = False
-- isImm (EBin {}) = False
-- isImm (ELam {}) = False
-- isImm (EApp {}) = False

{-@ measure isAnf @-}
isAnf :: Expr -> Bool
isAnf (EInt {})      = True
isAnf (EVar {})      = True
isAnf (ELet _ e1 e2) = isAnf e1 && isAnf e2
isAnf (EBin _ e1 e2) = isImm e1 && isImm e2
isAnf (EApp e1 e2)   = isImm e1 && isImm e2
isAnf (ELam _ e)     = isAnf e

{-@ type AnfExpr = {v:Expr | isAnf v} @-}
type AnfExpr = Expr

{-@ type ImmExpr = {v:Expr | isImm v} @-}
type ImmExpr = Expr

--------------------------------------------------------------------------------
-- | A Monad to get Fresh names
--------------------------------------------------------------------------------
type AnfM a = State Int a

--------------------------------------------------------------------------------
{-@ anf :: Expr -> AnfM AnfExpr @-}
--------------------------------------------------------------------------------
anf (EInt n) =
  return (EInt n)

anf (EVar x) =
  return (EVar x)

anf (ELet x e1 e2) = do
  a1 <- anf e1
  a2 <- anf e2
  return (ELet x a1 a2)

anf (EBin o e1 e2) = do
  (b1s, v1) <- imm e1
  (b2s, v2) <- imm e2
  return (mkLet (b1s ++ b2s) (EBin o v1 v2))

anf (ELam x e) = do
  a <- anf e
  return (ELam x a)

anf (EApp e1 e2) = do
  (b1s, v1) <- imm e1
  (b2s, v2) <- imm e2
  return (mkLet (b1s ++ b2s) (EApp v1 v2))

{-@ mkLet :: [(Var, AnfExpr)] -> AnfExpr -> AnfExpr @-}
mkLet []         e' = e'
mkLet ((x,e):bs) e' = ELet x e (mkLet bs e')

--------------------------------------------------------------------------------
{-@ imm :: Expr -> AnfM ([(Var, AnfExpr)], ImmExpr) @-}
--------------------------------------------------------------------------------
imm (EInt n)       = return ([], EInt n)
imm (EVar x)       = return ([], EVar x)
imm e@(ELet {})    = immExpr e
imm e@(ELam {})    = immExpr e
imm (EBin o e1 e2) = imm2 e1 e2 (EBin o)
imm (EApp e1 e2)   = imm2 e1 e2 EApp

{-@ immExpr :: Expr -> AnfM ([(Var, AnfExpr)], ImmExpr) @-}
immExpr e = do
  a <- anf e
  t <- fresh
  return ([(t, a)], EVar t)

imm2 :: Expr -> Expr -> (ImmExpr -> ImmExpr -> AnfExpr) -> AnfM ([(Var, AnfExpr)], ImmExpr)
imm2 e1 e2 f = do
  (b1s, v1) <- imm e1
  (b2s, v2) <- imm e2
  t         <- fresh
  let bs'    = b1s ++ b2s ++ [(t, f v1 v2)]
  return      (bs', EVar t)

--------------------------------------------------------------------------------
{-@ fresh :: AnfM Var @-}
--------------------------------------------------------------------------------
fresh = do
  n <- get
  put (n+1)
  return ("tmp" ++ show n)
