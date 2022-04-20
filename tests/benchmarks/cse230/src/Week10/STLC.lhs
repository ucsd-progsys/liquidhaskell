
The Simply Typed Lambda Calculus 
================================ 
  
A formalization of the Simply Typed Lambda Calculus (STLC) in the style 
of [Jeremy Siek](http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html)

\begin{code}
{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

{-# LANGUAGE GADTs #-}

module STLC where 

import ProofCombinators
\end{code}


Variables 
---------

\begin{code} 
type Var = String 
\end{code} 

Types and Environments
----------------------

\begin{code}
data Type 
  = TInt                     -- ^ `TInt`         is `Int`  
  | TBool                    -- ^ `TBool`        is `Bool`
  | TFun Type Type           -- ^ `TFun t1 t2`   is `t1 -> t2`
  deriving (Eq, Show) 

data TEnv                  
  = TBind Var Type TEnv      -- ^ x:t, G
  | TEmp                     -- ^ Empty environment
  deriving (Eq, Show) 
\end{code}

Terms 
-----

\begin{code}
data Op  
  = Add                      -- ^ `Add` is `+` 
  | Leq                      -- ^ `Leq` is `<=`
  | And                      -- ^ `And` is `&&`
  deriving (Eq, Show) 

data Expr 
  = EBool Bool               -- ^ 'EBool b'       is 'b'
  | EInt  Int                -- ^ 'EInt i'        is 'i'
  | EBin  Op Expr Expr       -- ^ 'EBin op e1 e2' is 'e1 `op` e2'
  | EVar  Var                -- ^ 'EVar x'        is 'x'
  | EFun  Var Var Type Expr  -- ^ 'EFun f x t e'  is 'fun f(x:t) e'
  | EApp  Expr Expr          -- ^ 'EApp e1 e2'    is 'e1 e2' 
  deriving (Eq, Show) 
\end{code}


Values and Stores 
-----------------

\begin{code}
data Val 
  = VBool Bool 
  | VInt  Int
  | VClos Var Var Expr Store
  deriving (Eq, Show) 

data Store  
  = VBind Var Val Store 
  | VEmp 
  deriving (Eq, Show) 
\end{code}


Evaluation Result 
-----------------

\begin{code}
data Result 
  = Result Val  
  | Stuck 
  | Timeout
  deriving (Eq, Show) 
\end{code}


Dynamic Semantics (Evaluator)
----------------------------- 

Big-Step? Small-Step?

\begin{code}
{-@ reflect eval @-}
eval :: Store -> Expr -> Result 
eval _   (EBool b)    = Result (VBool b)
eval _   (EInt  n)    = Result (VInt  n)
eval s (EBin o e1 e2) = seq2 (evalOp o) (eval s e1) (eval s e2) 
eval s (EVar x)       = case lookupStore x s of 
                          Nothing -> Stuck 
                          Just v  -> Result v 
eval s (EFun f x t e) = Result (VClos f x e s) 
eval s (EApp e1 e2)   = seq2 evalApp (eval s e1) (eval s e2)

{-@ reflect evalApp @-}
evalApp :: Val -> Val -> Result 
evalApp v1@(VClos f x e s) v2 = eval (VBind x v2 (VBind f v1 s)) e 
evalApp _                  _  = Stuck 

{-@ reflect evalOp @-}
evalOp :: Op -> Val -> Val -> Result 
evalOp Add (VInt n1)  (VInt n2)  = Result (VInt  (n1 +  n2))
evalOp Leq (VInt n1)  (VInt n2)  = Result (VBool (n1 <= n2))
evalOp And (VBool b1) (VBool b2) = Result (VBool (b1 && b2)) 
evalOp _   _          _          = Stuck 

{-@ reflect lookupStore @-}
lookupStore :: Var -> Store -> Maybe Val 
lookupStore x VEmp             = Nothing 
lookupStore x (VBind y v env)  = if x == y then Just v else lookupStore x env
\end{code}

Helper to *sequence* sub-computations.

\begin{code}
{-@ reflect seq2 @-}
seq2 :: (Val -> Val -> Result) -> Result -> Result -> Result
seq2 f r1 r2 = case r1 of 
                 Stuck     -> Stuck 
                 Timeout   -> Timeout 
                 Result v1 -> case r2 of 
                                Stuck     -> Stuck 
                                Timeout   -> Timeout 
                                Result v2 -> f v1 v2
\end{code}

Tests before proofs 
-------------------

\begin{code}
tests :: [Expr]
tests  = [ e1              -- 15
         , EBin Leq e1 e1  -- True
         , EBin And e1 e1  -- Stuck!
         ]
  where 
    e1 = EBin Add (EInt 5) (EInt 10)
\end{code}

Static Semantics (aka Static Typing Rules) 
------------------------------------------


**Typing Results** 

[ . |- r : T ]


    |- v : T 
  -------------------- [R_Res]
    |- Result v : T  

  -------------------- [R_Time]
    |- Timeout  : T  

\begin{code}
{-@ data ResTy where
        R_Res  :: x:Val -> t:Type -> Prop (ValTy x t) -> Prop (ResTy (Result x) t) 
        R_Time :: t:Type -> Prop (ResTy Timeout t) 
  @-}

data ResTyP where 
  ResTy  :: Result -> Type -> ResTyP 

data ResTy where 
  R_Res  :: Val -> Type -> ValTy -> ResTy 
  R_Time :: Type -> ResTy 
\end{code}

**Typing Values**

[ |- v : T ] 

    ----------------------- [V_Bool]
      |- VBool b : TBool

    ----------------------- [V_Int]
      |- VInt i : TInt 
   
    G |- s  (x,t1), (f,t1->t2),G |- e : t2 
    --------------------------------------- [V_Clos]
      |- VClos f x e s : t1 -> t2 

\begin{code}
{-@ data ValTy where
        V_Bool :: b:Bool -> Prop (ValTy (VBool b) TBool) 
        V_Int  :: i:Int  -> Prop (ValTy (VInt i)  TInt) 
        V_Clos :: g:TEnv -> s:Store -> f:Var -> x:Var -> t1:Type -> t2:Type -> e:Expr 
               -> Prop (StoTy g s) 
               -> Prop (ExprTy (TBind x t1 (TBind f (TFun t1 t2) g)) e t2)
               -> Prop (ValTy (VClos f x e s) (TFun t1 t2)) 
  @-}

data ValTyP where 
  ValTy  :: Val -> Type -> ValTyP 

data ValTy where 
  V_Bool :: Bool -> ValTy 
  V_Int  :: Int  -> ValTy 
  V_Clos :: TEnv -> Store -> Var -> Var -> Type -> Type -> Expr -> StoTy -> ExprTy  -> ValTy 
\end{code}

**Typing Stores**

[ G |- S ] 

   ------------------------[S_Emp]
   TEmp |- VEmp 

      |- v : t   g |- s 
   ------------------------[S_Bind]
   (x, t), g |- (x, v), s 

\begin{code}
{-@ data StoTy where
        S_Emp  :: Prop (StoTy TEmp VEmp) 
        S_Bind :: x:Var -> t:Type -> val:Val -> g:TEnv -> s:Store
               -> Prop (ValTy val t) 
               -> Prop (StoTy g   s) 
               -> Prop (StoTy (TBind x t g) (VBind x val s)) 
  @-}

data StoTyP where 
  StoTy  :: TEnv -> Store -> StoTyP 

data StoTy where 
  S_Emp  :: StoTy 
  S_Bind :: Var -> Type -> Val -> TEnv -> Store -> ValTy -> StoTy -> StoTy 
\end{code}

**Typing Expressions**

  --------------------------------------[E-Bool]
    G |- EBool b : TBool

  --------------------------------------[E-Int]
    G |- EInt n  : TInt 

    lookupTEnv x G = Just t
  --------------------------------------[E-Var]
    G |- Var x  : t 

    G |- e1 : opIn o  G |- e2 : opIn o 
  --------------------------------------[E-Bin]
    G |- EBin o e1 e2 : opOut o


    (x,t1), (f, t1->t2), G |- e : t2 
  --------------------------------------[E-Fun]
    G |- EFun f x t1 e : t1 -> t2 

    G |- e1 : t1 -> t2   G |- e2 : t1 
  --------------------------------------[E-App]
    G |- EApp e1 e2 : t2 

\begin{code}
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


{-@ data ExprTy where 
        E_Bool :: g:TEnv -> b:Bool 
               -> Prop (ExprTy g (EBool b) TBool)
        E_Int  :: g:TEnv -> i:Int  
               -> Prop (ExprTy g (EInt i)  TInt)
        E_Bin  :: g:TEnv -> o:Op -> e1:Expr -> e2:Expr 
               -> Prop (ExprTy g e1 (opIn o)) 
               -> Prop (ExprTy g e2 (opIn o))
               -> Prop (ExprTy g (EBin o e1 e2) (opOut o))
        E_Var  :: g:TEnv -> x:Var -> t:{Type| lookupTEnv x g == Just t} 
               -> Prop (ExprTy g (EVar x) t)
        E_Fun  :: g:TEnv -> f:Var -> x:Var -> t1:Type -> e:Expr -> t2:Type
               -> Prop (ExprTy (TBind x t1 (TBind f (TFun t1 t2) g)) e t2)
               -> Prop (ExprTy g (EFun f x t1 e) (TFun t1 t2))       
        E_App  :: g:TEnv -> e1:Expr -> e2:Expr -> t1:Type -> t2:Type 
               -> Prop (ExprTy g e1 (TFun t1 t2))
               -> Prop (ExprTy g e2 t1)
               -> Prop (ExprTy g (EApp e1 e2) t2)
  @-}
data ExprTyP where 
  ExprTy :: TEnv -> Expr -> Type -> ExprTyP  

data ExprTy where 
  E_Bool :: TEnv -> Bool -> ExprTy 
  E_Int  :: TEnv -> Int  -> ExprTy 
  E_Var  :: TEnv -> Var  -> Type -> ExprTy 
  E_Bin  :: TEnv -> Op   -> Expr -> Expr -> ExprTy -> ExprTy -> ExprTy 
  E_Fun  :: TEnv -> Var -> Var -> Type -> Expr -> Type -> ExprTy -> ExprTy 
  E_App  :: TEnv -> Expr -> Expr -> Type -> Type -> ExprTy -> ExprTy -> ExprTy 
\end{code}

Lemma 1: "evalOp_safe" 
----------------------


\begin{code}
{-@ reflect isValTy @-}
isValTy :: Val -> Type -> Bool 
isValTy (VInt _)  TInt  = True 
isValTy (VBool _) TBool = True 
isValTy _         _     = False 

{-@ propValTy :: o:Op -> w:Val -> Prop (ValTy w (opIn o)) -> { w' : Val | w = w' && isValTy w' (opIn o) } @-}
propValTy :: Op -> Val -> ValTy -> Val 
propValTy Add w (V_Int _) = w 
propValTy Leq w (V_Int _)  = w 
propValTy And w (V_Bool _) = w 

{-@ evalOp_safe 
      :: o:Op -> v1:{Val | isValTy v1 (opIn o) } -> v2:{Val | isValTy v2 (opIn o) } 
      -> (v :: Val, ( {y:() | evalOp o v1 v2 == Result v} , {z:ValTy | prop z = ValTy v (opOut o)}))
  @-}
evalOp_safe :: Op -> Val -> Val -> (Val, ((), ValTy))
evalOp_safe Add (VInt n1) (VInt n2)   = (VInt n, ((), V_Int n))   where n = n1 + n2 
evalOp_safe Leq (VInt n1) (VInt n2)   = (VBool b, ((), V_Bool b)) where b = n1 <= n2 
evalOp_safe And (VBool b1) (VBool b2) = (VBool b, ((), V_Bool b)) where b = b1 && b2 

{-@ evalOp_res_safe 
      :: o:Op -> r1:Result -> r2:Result
      -> Prop (ResTy r1 (opIn o))
      -> Prop (ResTy r2 (opIn o))
      -> Prop (ResTy (seq2 (evalOp o) r1 r2) (opOut o)) 
  @-}
evalOp_res_safe :: Op -> Result -> Result -> ResTy -> ResTy -> ResTy
evalOp_res_safe o (Result v1) (Result v2) (R_Res _ t1 vt1) (R_Res _ t2 vt2) 
  = case evalOp_safe o (propValTy o v1 vt1) (propValTy o v2 vt2) of 
      (v, (_, vt)) -> R_Res v (opOut o) vt  
evalOp_res_safe o _ _  (R_Time t1) _ 
  = R_Time (opOut o)
evalOp_res_safe o _ _  _ (R_Time t2) 
  = R_Time (opOut o)
\end{code}

Lemma 2: "lookup_safe"
----------------------

\begin{code}
{-@ lookup_safe :: g:TEnv -> s:Store -> x:Var -> t:{Type | lookupTEnv x g == Just t} 
                -> Prop (StoTy g s) 
                -> (w :: Val, ({z:() | lookupStore x s ==  Just w} , {z:ValTy | prop z = ValTy w t} ))
  @-}
lookup_safe :: TEnv -> Store -> Var -> Type -> StoTy -> (Val, ((), ValTy)) 
lookup_safe _ _ _ _ S_Emp 
  = impossible () 
lookup_safe g s x t (S_Bind y yt yv g' s' yvt gs')  
  | x == y 
  = (yv, ((), yvt)) 
  | otherwise 
  = lookup_safe g' s' x t gs' 
\end{code}

Lemma 3: "app_safe" 
-------------------

\begin{code}
{-@ evalApp_safe 
      :: v1:Val -> v2:Val -> t1:Type -> t2:Type
      -> Prop (ValTy v1 (TFun t1 t2)) 
      -> Prop (ValTy v2 t1)
      -> Prop (ResTy (evalApp v1 v2) t2) 
  @-}
evalApp_safe :: Val -> Val -> Type -> Type -> ValTy -> ValTy -> ResTy 
evalApp_safe v1@(VClos f x e s) v2 t1 t2 v1_t1_t2@(V_Clos g _ _ _ _ _ _ g_s gxf_e_t2) v2_t1 
  = eval_safe gxf sxf e t2 gxf_e_t2 gxf_sxf  
  where 
    gf      = TBind f (TFun t1 t2) g
    sf      = VBind f v1           s
    gxf     = TBind x t1 gf 
    sxf     = VBind x v2 sf  
    gf_sf   = S_Bind f (TFun t1 t2) v1 g  s  v1_t1_t2 g_s 
    gxf_sxf = S_Bind x t1           v2 gf sf v2_t1    gf_sf             
    
evalApp_safe (VInt {}) _ _ _ (V_Clos {}) _ 
  = impossible () 

evalApp_safe (VBool {}) _ _ _ (V_Clos {}) _ 
  = impossible () 




{-@ evalApp_res_safe 
      :: r1:Result -> r2:Result -> t1:Type -> t2:Type
      -> Prop (ResTy r1 (TFun t1 t2)) 
      -> Prop (ResTy r2 t1)
      -> Prop (ResTy (seq2 evalApp r1 r2) t2)
  @-}
evalApp_res_safe :: Result -> Result -> Type -> Type -> ResTy -> ResTy -> ResTy 
evalApp_res_safe (Result v1) (Result v2) t1 t2 (R_Res _ _ v1_t1_t2) (R_Res _ _ v2_t1)
  = evalApp_safe v1 v2 t1 t2 v1_t1_t2 v2_t1 
evalApp_res_safe _ _ _ t2 (R_Time {}) _ 
  = R_Time t2 
evalApp_res_safe _ _ _ t2 _ (R_Time {}) 
  = R_Time t2 
\end{code}

THEOREM: "eval_safe" 
--------------------

\begin{code}
{-@ eval_safe :: g:TEnv -> s:Store -> e:Expr -> t:Type 
              -> Prop (ExprTy g e t) 
              -> Prop (StoTy  g s) 
              -> Prop (ResTy (eval s e) t) 
  @-}
eval_safe :: TEnv -> Store -> Expr -> Type -> ExprTy -> StoTy -> ResTy 

eval_safe _ _ (EBool b) _ (E_Bool {}) _          
  = R_Res (VBool b) TBool (V_Bool b) 
 
eval_safe _ _ (EInt n) _ (E_Int {}) _ 
  = R_Res (VInt n) TInt (V_Int n) 

eval_safe g s (EBin o e1 e2) t (E_Bin _ _ _ _ et1 et2) gs
  = evalOp_res_safe o (eval s e1) (eval s e2) rt1 rt2     
  where 
    rt1          = eval_safe g s e1 (opIn o) et1 gs
    rt2          = eval_safe g s e2 (opIn o) et2 gs

eval_safe g s (EVar x) t (E_Var {}) gs     
  = R_Res w t wt 
  where 
    (w, (_, wt)) = lookup_safe g s x t gs 

eval_safe g s (EFun f x t1 e) t (E_Fun _ _ _ _ _ t2 et2) gs 
  = R_Res (VClos f x e s) t (V_Clos g s f x t1 t2 e gs et2)
      
eval_safe g s (EApp e1 e2) t2 (E_App _ _ _ t1 _ e1_t1_t2 e2_t1) gs 
  = evalApp_res_safe (eval s e1) (eval s e2) t1 t2 r1_t1_t2 r2_t1 
  where 
    r1_t1_t2 = eval_safe g s e1 (TFun t1 t2) e1_t1_t2 gs 
    r2_t1    = eval_safe g s e2 t1           e2_t1    gs
\end{code} 

Boilerplate 
-----------

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

{-@ impossible :: {v:a | false} -> b @-}
impossible :: a -> b
impossible x = impossible x  
