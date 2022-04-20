-- http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html 

{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

{-# LANGUAGE GADTs #-}

module STLCB0 where


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

{-@ reflect seq2 @-}
-- seq2 :: (a -> b -> Result c) -> Result a -> Result b -> Result c
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
eval :: Expr -> Result 
eval (EBool b)      = Result (VBool b)
eval (EInt  n)      = Result (VInt  n)
eval (EBin o e1 e2) = seq2 (evalOp o) (eval e1) (eval e2) 

{-@ reflect evalOp @-}
evalOp :: Op -> Val -> Val -> Result 
evalOp Add (VInt n1)  (VInt n2)  = Result (VInt  (n1 +  n2))
evalOp Leq (VInt n1)  (VInt n2)  = Result (VBool (n1 <= n2))
evalOp And (VBool b1) (VBool b2) = Result (VBool (b1 && b2)) 
evalOp _   _          _          = Stuck 

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
isExprTy :: Expr -> Type -> Bool 
isExprTy (EBool _)       TBool = True 
isExprTy (EInt _)        TInt  = True 
isExprTy (EBin o e1 e2)  t     = isExprTy e1 (opIn o) 
                              && isExprTy e2 (opIn o) 
                              && opOut o == t 
isExprTy _               _     = False 

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
evalOp_res_safe Add (Result v1) (Result v2) = evalOp_safe Add v1 v2
evalOp_res_safe Leq (Result v1) (Result v2) = evalOp_safe Leq v1 v2
evalOp_res_safe And (Result v1) (Result v2) = evalOp_safe And v1 v2
evalOp_res_safe o _ _                     = () 

--------------------------------------------------------------------------------
-- | Lemma 3: "eval_safe" 
--------------------------------------------------------------------------------

{-@ eval_safe :: e:Expr -> t:{Type | isExprTy e t} -> { isResTy (eval e) t } @-}
eval_safe :: Expr -> Type -> () 
eval_safe (EBool _) TBool  = () 
eval_safe (EInt _)  TInt   = () 
eval_safe (EBin o e1 e2) t = evalOp_res_safe o r1 r2 
  where 
    r1                     = eval e1 `withProof` (eval_safe e1 (opIn o))
    r2                     = eval e2 `withProof` (eval_safe e2 (opIn o))

--------------------------------------------------------------------------------
-- | Boilerplate 
--------------------------------------------------------------------------------

{-@ withProof :: x:a -> b -> {v:a | v = x} @-}
withProof :: a -> b -> a
withProof x y = x

