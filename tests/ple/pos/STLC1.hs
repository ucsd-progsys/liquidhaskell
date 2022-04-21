-- http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html 

{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

{-# LANGUAGE GADTs #-}

module STLC1 where

type Var = String 

data Type 
  = TInt 
  | TBool 
  deriving (Eq, Show) 
 -- | TFun Type Type 

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

{-@ reflect lookupVEnv @-}
lookupVEnv :: Var -> VEnv -> Maybe Val 
lookupVEnv x VEmp             = Nothing 
lookupVEnv x (VBind y v env)  = if x == y then Just v else lookupVEnv x env

{-@ reflect eval @-}
eval :: VEnv -> Expr -> Result 
eval _   (EBool b)    = Result (VBool b)
eval _   (EInt  n)    = Result (VInt  n)
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

{- [ |- r : T ]


    |- v : T 
  -------------------- [R_Res]
    |- Result v : T  

  -------------------- [R_Time]
    |- Timeout  : T  

-}

{-@ data ResTy where
        R_Res  :: x:Val -> t:Type -> Prop (ValTy x t) -> Prop (ResTy (Result x) t) 
        R_Time :: t:Type -> Prop (ResTy Timeout t) 
  @-}

data ResTyP where 
  ResTy  :: Result -> Type -> ResTyP 

data ResTy where 
  R_Res  :: Val -> Type -> ValTy -> ResTy 
  R_Time :: Type -> ResTy 

--------------------------------------------------------------------------------
-- | Typing Values 
--------------------------------------------------------------------------------

{- [ |- v : T ] 

    ----------------------- [V_Bool]
      |- VBool b : TBool

    ----------------------- [V_Int]
      |- VInt i : TInt 
    
 -}

{-@ data ValTy where
        V_Bool :: b:Bool -> Prop (ValTy (VBool b) TBool) 
        V_Int  :: i:Int  -> Prop (ValTy (VInt i)  TInt) 
  @-}

data ValTyP where 
  ValTy  :: Val -> Type -> ValTyP 

data ValTy where 
  V_Bool :: Bool -> ValTy 
  V_Int  :: Int  -> ValTy 

--------------------------------------------------------------------------------
-- | Typing Stores 
--------------------------------------------------------------------------------

{- [ G |- S ] 

   ------------------------[S_Emp]
   TEmp |- VEmp 

      |- v : t   g |- s 
   ------------------------[S_Bind]
   (x, t), g |- (x, v), s 

 -}

{-@ data StoTy where
        S_Emp  :: Prop (StoTy TEmp VEmp) 
        S_Bind :: x:Var -> t:Type -> val:Val -> g:TEnv -> s:VEnv
               -> Prop (ValTy val t) 
               -> Prop (StoTy g   s) 
               -> Prop (StoTy (TBind x t g) (VBind x val s)) 
  @-}

data StoTyP where 
  StoTy  :: TEnv -> VEnv -> StoTyP 

data StoTy where 
  S_Emp  :: StoTy 
  S_Bind :: Var -> Type -> Val -> TEnv -> VEnv -> ValTy -> StoTy -> StoTy 

--------------------------------------------------------------------------------
-- | Typing Expressions 
--------------------------------------------------------------------------------

{-@ reflect opIn1 @-}
opIn1 :: Op -> Type 
opIn1 Add = TInt 
opIn1 Leq = TInt 
opIn1 And = TBool

{-@ reflect opIn2 @-}
opIn2 :: Op -> Type 
opIn2 Add = TInt 
opIn2 Leq = TInt 
opIn2 And = TBool

{-@ reflect opOut @-}
opOut :: Op -> Type 
opOut Add = TInt 
opOut Leq = TBool 
opOut And = TBool

{-@ reflect lookupTEnv @-}
lookupTEnv :: Var -> TEnv -> Maybe Type 
lookupTEnv x TEmp             = Nothing 
lookupTEnv x (TBind y v env)  = if x == y then Just v else lookupTEnv x env


{- 

  --------------------------------------[E-Bool]
    G |- EBool b : TBool

  --------------------------------------[E-Int]
    G |- EInt n  : TInt 

    lookupTEnv x G = Just t
  --------------------------------------[E-Var]
    G |- Var x  : t 

    G |- e1 : opIn1 o  G |- e2 : opIn2 o 
  --------------------------------------[E-Bin]
    G |- EBin o e1 e2 : opOut o

-}

{-@ data ExprTy where 
        E_Bool :: g:TEnv -> b:Bool 
               -> Prop (ExprTy g (EBool b) TBool)
        E_Int  :: g:TEnv -> i:Int  
               -> Prop (ExprTy g (EInt i)  TInt)
        E_Bin  :: g:TEnv -> o:Op -> e1:Expr -> e2:Expr 
               -> Prop (ExprTy g e1 (opIn1 o)) 
               -> Prop (ExprTy g e2 (opIn2 o))
               -> Prop (ExprTy g (EBin o e1 e2) (opOut o))
        E_Var  :: g:TEnv -> x:Var -> t:{Type| lookupTEnv x g == Just t} 
               -> Prop (ExprTy g (EVar x) t)
  @-}
data ExprTyP where 
  ExprTy :: TEnv -> Expr -> Type -> ExprTyP  

data ExprTy where 
  E_Bool :: TEnv -> Bool -> ExprTy 
  E_Int  :: TEnv -> Int  -> ExprTy 
  E_Var  :: TEnv -> Var  -> Type -> ExprTy 
  E_Bin  :: TEnv -> Op   -> Expr -> Expr -> ExprTy -> ExprTy -> ExprTy 

--------------------------------------------------------------------------------
-- | Lemma 1: "evalOp_safe" 
--------------------------------------------------------------------------------

{-@ evalOp_safe 
      :: o:Op -> v1:Val -> v2:Val 
      -> Prop (ValTy v1 (opIn1 o)) 
      -> Prop (ValTy v2 (opIn2 o)) 
      -> (v :: Val, ( {y:() | evalOp o v1 v2 == Result v} , {z:ValTy | prop z = ValTy v (opOut o)}))
  @-}

evalOp_safe :: Op -> Val -> Val -> ValTy -> ValTy -> (Val, ((), ValTy))
evalOp_safe Add (VInt n1) (VInt n2) _ _   = (VInt n, ((), V_Int n))   where n = n1 + n2 
evalOp_safe Add (VBool _) _ (V_Int _) _   = trivial () 
evalOp_safe Add _ (VBool _) _ (V_Int _)   = trivial () 

evalOp_safe Leq (VInt n1) (VInt n2) _ _   = (VBool b, ((), V_Bool b)) where b = n1 <= n2 
evalOp_safe Leq (VBool _) _ (V_Int _) _   = trivial () 
evalOp_safe Leq _ (VBool _) _ (V_Int _)   = trivial () 

evalOp_safe And (VBool b1) (VBool b2) _ _ = (VBool b, ((), V_Bool b)) where b = b1 && b2 
evalOp_safe And (VInt _) _ (V_Bool _) _   = trivial () 
evalOp_safe And _ (VInt _) _ (V_Bool _)   = trivial () 

{-@ evalOp_res_safe 
      :: o:Op -> r1:Result -> r2:Result
      -> Prop (ResTy r1 (opIn1 o))
      -> Prop (ResTy r2 (opIn2 o))
      -> Prop (ResTy (seq2 (evalOp o) r1 r2) (opOut o)) 
  @-}
evalOp_res_safe :: Op -> Result -> Result -> ResTy -> ResTy -> ResTy
evalOp_res_safe o (Result v1) (Result v2) (R_Res _ _ vt1) (R_Res _ _ vt2) 
  = case evalOp_safe o v1 v2 vt1 vt2 of 
      (v, (_, vt)) -> R_Res v (opOut o) vt  
evalOp_res_safe o _ _  (R_Time t1) _ 
  = R_Time (opOut o)
evalOp_res_safe o _ _  _ (R_Time t2) 
  = R_Time (opOut o)

--------------------------------------------------------------------------------
-- | Lemma 2: "lookup_safe"
--------------------------------------------------------------------------------
{-@ lookup_safe :: g:TEnv -> s:VEnv -> x:Var -> t:{Type | lookupTEnv x g == Just t} 
                -> Prop (StoTy g s) 
                -> (w :: Val, ({z:() | lookupVEnv x s ==  Just w} , {z:ValTy | prop z = ValTy w t} ))
  @-}
lookup_safe :: TEnv -> VEnv -> Var -> Type -> StoTy -> (Val, ((), ValTy)) 
lookup_safe _ _ _ _ S_Emp 
  = trivial () 
lookup_safe g s x t (S_Bind y yt yv g' s' yvt gs')  
  | x == y 
  = (yv, ((), yvt)) 
  | otherwise 
  = lookup_safe g' s' x t gs' 

--------------------------------------------------------------------------------
-- | Lemma 3: "eval_safe" 
--------------------------------------------------------------------------------

{-@ eval_safe :: g:TEnv -> s:VEnv -> e:Expr -> t:Type 
              -> Prop (ExprTy g e t) 
              -> Prop (StoTy  g s) 
              -> Prop (ResTy (eval s e) t) 
  @-}
eval_safe :: TEnv -> VEnv -> Expr -> Type -> ExprTy -> StoTy -> ResTy 
eval_safe _ _ (EBool b) TBool _ _          
  = R_Res (VBool b) TBool (V_Bool b) 
eval_safe _ _ (EBool _) _     (E_Int {}) _ 
  = trivial ()  -- WHY is this needed?
 
eval_safe _ _ (EInt n) TInt  _           _ 
  = R_Res (VInt n) TInt (V_Int n) 
eval_safe _ _ (EInt _) _     (E_Bool {}) _ 
  = trivial ()  -- WHY is this needed?

eval_safe g s (EBin o e1 e2) t (E_Bin _ _ _ _ et1 et2) gs
  = evalOp_res_safe o (eval s e1) (eval s e2) rt1 rt2     
  where 
    rt1          = eval_safe g s e1 (opIn1 o) et1 gs
    rt2          = eval_safe g s e2 (opIn2 o) et2 gs

eval_safe g s (EVar x) t (E_Var {}) gs     
  = R_Res w t wt 
  where 
    (w, (_, wt)) = lookup_safe g s x t gs 

--------------------------------------------------------------------------------
-- | Boilerplate 
--------------------------------------------------------------------------------

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

{-@ trivial :: {v:a | false} -> b @-}
trivial :: a -> b
trivial x = trivial x  
