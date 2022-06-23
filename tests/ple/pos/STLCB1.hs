-- http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html

{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

{-# LANGUAGE GADTs #-}

module STLCB1 where

import Language.Haskell.Liquid.ProofCombinators ((?))

type Var = String

data Type
  = TInt
  | TBool
  deriving (Eq, Show)

data Op
  = Add
  | Leq
  | And
  deriving (Eq, Show)

data Expr
  = EBool Bool
  | EInt  Int
  | EBin  Op Expr Expr
  | EVar  Var
  deriving (Eq, Show)

data Val
  = VBool Bool
  | VInt  Int
  deriving (Eq, Show)

data Result
  = Result Val
  | Stuck
  | Timeout
  deriving (Eq, Show)

data VEnv
  = VBind Var Val VEnv
  | VEmp
  deriving (Eq, Show)

data TEnv
  = TBind Var Type TEnv
  | TEmp
  deriving (Eq, Show)


{-@ reflect seq2 @-}
seq2 :: (Val -> Val -> Result) -> Result -> Result -> Result
seq2 f r1 r2 = case r1 of
                 Stuck     -> Stuck
                 Timeout   -> Timeout
                 Result v1 -> case r2 of
                                Stuck     -> Stuck
                                Timeout   -> Timeout
                                Result v2 -> f v1 v2

--------------------------------------------------------------------------------
-- | Evaluator
--------------------------------------------------------------------------------

{-@ reflect eval @-}
eval :: VEnv -> Expr -> Result
eval _ (EBool b)      = Result (VBool b)
eval _ (EInt  n)      = Result (VInt  n)
eval s (EBin o e1 e2) = seq2 (evalOp o) (eval s e1) (eval s e2)
eval s (EVar x)       = case lookupVEnv x s of
                          Nothing -> Stuck
                          Just v  -> Result v


{-@ reflect evalOp @-}
evalOp :: Op -> Val -> Val -> Result
evalOp Add (VInt n1)  (VInt n2)  = Result (VInt  (n1 +  n2))
evalOp Leq (VInt n1)  (VInt n2)  = Result (VBool (n1 <= n2))
evalOp And (VBool b1) (VBool b2) = Result (VBool (b1 && b2))
evalOp _   _          _          = Stuck

{-@ reflect lookupVEnv @-}
lookupVEnv :: Var -> VEnv -> Maybe Val
lookupVEnv x VEmp             = Nothing
lookupVEnv x (VBind y v env)  = if x == y then Just v else lookupVEnv x env


--------------------------------------------------------------------------------
-- | Tests before proofs
--------------------------------------------------------------------------------

tests  = [ e1              -- 15
         , EBin Leq e1 e1  -- True
         , EBin And e1 e1  -- Stuck!
         ]
  where
    e1 = EBin Add (EInt 5) (EInt 10)


--------------------------------------------------------------------------------
-- | Typing Results
--------------------------------------------------------------------------------

{-@ reflect isResTy @-}
isResTy :: Result -> Type -> Bool
isResTy (Result v) t = isValTy v t
isResTy Timeout    _ = True
isResTy Stuck      _ = False

--------------------------------------------------------------------------------
-- | Typing Values
--------------------------------------------------------------------------------

{-@ reflect isValTy @-}
isValTy :: Val -> Type -> Bool
isValTy (VBool _) TBool = True
isValTy (VInt _)  TInt  = True
isValTy _         _     = False

--------------------------------------------------------------------------------
-- | Typing Expressions
--------------------------------------------------------------------------------

{-@ reflect isExprTy @-}
isExprTy :: TEnv -> Expr -> Type -> Bool
isExprTy _ (EBool _)       TBool = True
isExprTy _ (EInt _)        TInt  = True
isExprTy g (EBin o e1 e2)  t     = isExprTy g e1 (opIn o)
                                && isExprTy g e2 (opIn o)
                                && opOut o == t
isExprTy g (EVar x)        t     = lookupTEnv x g == Just t
isExprTy _ _               _     = False

{-@ reflect opIn @-}
opIn :: Op -> Type
opIn Add = TInt
opIn Leq = TInt
opIn And = TBool

{-@ reflect opOut @-}
opOut :: Op -> Type
opOut Add = TInt
opOut Leq = TBool
opOut And = TBool

{-@ reflect lookupTEnv @-}
lookupTEnv :: Var -> TEnv -> Maybe Type
lookupTEnv x TEmp             = Nothing
lookupTEnv x (TBind y v env)  = if x == y then Just v else lookupTEnv x env


--------------------------------------------------------------------------------
-- | Typing Stores
--------------------------------------------------------------------------------
{-@ reflect isStoTy @-}
isStoTy :: TEnv -> VEnv -> Bool
isStoTy TEmp VEmp                   = True
isStoTy (TBind x t g) (VBind y v s) = x == y
                                   && isValTy v t
                                   && isStoTy g s
isStoTy _             _             = False

--------------------------------------------------------------------------------
-- | Lemma 1: "evalOp_safe"
--------------------------------------------------------------------------------

{-@ evalOp_safe
      :: o:Op -> v1:{Val | isValTy v1 (opIn o)} -> v2:{Val | isValTy v2 (opIn o)}
      -> { isResTy (evalOp o v1 v2) (opOut o) }
  @-}

evalOp_safe :: Op -> Val -> Val -> ()
evalOp_safe Add (VInt n1) (VInt n2) = ()
evalOp_safe Leq (VInt n1) (VInt n2) = ()
evalOp_safe And (VBool _) (VBool _) = ()

{-@ evalOp_res_safe
      :: o:Op -> r1:{Result | isResTy r1 (opIn o)} -> r2:{Result | isResTy r2 (opIn o)}
      -> { isResTy (seq2 (evalOp o) r1 r2) (opOut o) }
  @-}
evalOp_res_safe :: Op -> Result -> Result -> ()
evalOp_res_safe o (Result v1) (Result v2) = evalOp_safe o v1 v2
evalOp_res_safe o _ _                     = ()

--------------------------------------------------------------------------------
-- | Lemma 2: "lookup_safe"
--------------------------------------------------------------------------------
{-@ lookup_safe
      :: g:TEnv -> s:{VEnv | isStoTy g s} -> x:Var -> t:{Type | lookupTEnv x g == Just t}
      -> (w :: Val, {z:() | lookupVEnv x s ==  Just w && isValTy w t})
  @-}
lookup_safe :: TEnv -> VEnv -> Var -> Type -> (Val, ())
lookup_safe (TBind x1 _ g) (VBind _ v s) x t
  | x == x1
  = (v, ())
  | otherwise
  = lookup_safe g s x t

--------------------------------------------------------------------------------
-- | Lemma 3: "eval_safe"
--------------------------------------------------------------------------------
{-@ eval_safe
      :: g:TEnv -> s:{VEnv | isStoTy g s} -> e:Expr -> t:{Type | isExprTy g e t}
      -> {isResTy (eval s e) t}
  @-}
eval_safe :: TEnv -> VEnv -> Expr -> Type -> ()
eval_safe _ _ (EBool _) TBool  = ()
eval_safe _ _ (EInt _)  TInt   = ()
eval_safe g s (EBin o e1 e2) t = evalOp_res_safe o r1 r2
  where
    r1                         = eval s e1
             `withProof` (eval_safe g s e1 (opIn o))
    r2                         = eval s e2
             `withProof` (eval_safe g s e2 (opIn o))
eval_safe g s (EVar x)       t = case lookup_safe g s x t of
             (_, prf) -> prf
  -- where
  --  (_, pf)                    = lookup_safe g s x t

--------------------------------------------------------------------------------
-- | Boilerplate
--------------------------------------------------------------------------------

{-@ withProof :: forall a b <pa :: a -> Bool, pb :: b -> Bool>. x:a<pa> -> b<pb> -> {v:a<pa> | v = x} @-}
withProof :: a -> b -> a
withProof x y = x

{- withProof :: x:a -> b -> {v:a | v = x} @-}

