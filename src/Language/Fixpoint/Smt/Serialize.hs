{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}

-- | This module contains the code for serializing Haskell values
--   into SMTLIB2 format, that is, the instances for the @SMTLIB2@
--   typeclass. We split it into a separate module as it depends on
--   Theories (see @smt2App@).

module Language.Fixpoint.Smt.Serialize where

import           Language.Fixpoint.Types
--import           Language.Fixpoint.Types.Names (mulFuncName, divFuncName)
import           Language.Fixpoint.Smt.Types
import qualified Language.Fixpoint.Smt.Theories as Thy
import qualified Data.Text                      as T
import           Data.Text.Format               hiding (format)
import           Data.Maybe (fromMaybe)
import           Language.Fixpoint.Misc (errorstar)

import           Language.Fixpoint.SortCheck (sortExpr)

{-
    (* (L t1 t2 t3) is now encoded as
        ---> (((L @ t1) @ t2) @ t3)
        ---> App(@, [App(@, [App(@, [L[]; t1]); t2]); t3])
        The following decodes the above as
     *)
    let rec app_args_of_t acc = function
      | App (c, [t1; t2]) when c = tc_app -> app_args_of_t (t2 :: acc) t1
      | App (c, [])                       -> (c, acc)
      | t                                 -> (tc_app, t :: acc)

      (*
      | Ptr (Loc s)                       -> (tycon s, acc)
      | t                                 -> assertf "app_args_of_t: unexpected t1 = %s" (to_string t)
      *)

    let app_of_t = function
      | App (c, _) as t when c = tc_app   -> Some (app_args_of_t [] t)
      | App (c, ts)                       -> Some (c, ts)
      | _                                 -> None

-}
instance SMTLIB2 Sort where
  smt2 _ s@(FFunc _ _)           = errorstar $ "smt2 FFunc: " ++ show s
  smt2 _ FInt                    = "Int"
  smt2 _ FReal                   = "Real"
  smt2 _ t
    | t == boolSort            = "Bool"
  smt2 _ t
    | Just d <- Thy.smt2Sort t = d
  smt2 _ _                       = "Int"


instance SMTLIB2 Symbol where
  smt2 _ s
    | Just t <- Thy.smt2Symbol s = t
  smt2 _ s                         = symbolSafeText  s

instance SMTLIB2 (Symbol, Sort) where
  smt2 env (sym, t) = format "({} {})"  (smt2 env sym, smt2 env t)

instance SMTLIB2 SymConst where
  smt2 env = smt2 env . symbol

instance SMTLIB2 Constant where
  smt2 _ (I n)   = format "{}" (Only n)
  smt2 _ (R d)   = format "{}" (Only d)
  smt2 _ (L t _) = format "{}" (Only t) -- errorstar $ "Horrors, how to translate: " ++ show c

instance SMTLIB2 LocSymbol where
  smt2 env = smt2 env . val

instance SMTLIB2 Bop where
  smt2 _ Plus  = "+"
  smt2 _ Minus = "-"
  smt2 _ Times = "*"
  smt2 _ Div   = "/"
  smt2 _ Mod   = "mod"

instance SMTLIB2 Brel where
  smt2 _ Eq    = "="
  smt2 _ Ueq   = "="
  smt2 _ Gt    = ">"
  smt2 _ Ge    = ">="
  smt2 _ Lt    = "<"
  smt2 _ Le    = "<="
  smt2 _ _     = errorstar "SMTLIB2 Brel"

-- NV TODO: change the way EApp is printed 
instance SMTLIB2 Expr where
  smt2 env (ESym z)         = smt2 env (symbol z)
  smt2 env (ECon c)         = smt2 env c
  smt2 env (EVar x)         = smt2 env x
  smt2 env e@(EApp _ _)     = smt2App env e
  smt2 env (ENeg e)         = format "(- {})"         (Only $ smt2 env e)
  smt2 env (EBin o e1 e2)   = smt2Bop env o e1 e2
  smt2 env (EIte e1 e2 e3)  = format "(ite {} {} {})" (smt2 env e1, smt2 env e2, smt2 env e3)
  smt2 env (ECst e _)       = smt2 env e
  smt2 _   (PTrue)          = "true"
  smt2 _   (PFalse)         = "false"
  smt2 _   (PAnd [])        = "true"
  smt2 env (PAnd ps)        = format "(and {})"    (Only $ smt2s env ps)
  smt2 _   (POr [])         = "false"
  smt2 env (POr ps)         = format "(or  {})"    (Only $ smt2s env ps)
  smt2 env (PNot p)         = format "(not {})"    (Only $ smt2  env p)
  smt2 env (PImp p q)       = format "(=> {} {})"  (smt2 env p, smt2 env q)
  smt2 env (PIff p q)       = format "(=  {} {})"  (smt2 env p, smt2 env q)
  smt2 env (PExist bs p)    = format "(exists ({}) {})"  (smt2s env bs, smt2 env p)
  smt2 env (PAtom r e1 e2)  = mkRel env r e1 e2
  smt2 _   _                = errorstar "smtlib2 Pred"

smt2Bop env o e1 e2
  | o == Times || o == Div = smt2App env (mkEApp (uOp o) [e1, e2])
  | otherwise  = format "({} {} {})" (smt2 env o, smt2 env e1, smt2 env e2)

uOp o | o == Times = dummyLoc mulFuncName
      | o == Div   = dummyLoc divFuncName
      | otherwise  = errorstar "Serialize.uOp called with bad arguments"

smt2App :: SMTEnv -> Expr  -> T.Text
smt2App env e = fromMaybe (smt2App' env f es) (Thy.smt2App f ds)
  where
    (f, es) = splitEApp e 
    ds      = smt2 env <$> es

smt2App' :: SMTEnv -> Expr -> [Expr] -> T.Text
smt2App' env f [] = smt2 env f
smt2App' env f es = makeApplication env f es 
-- smt2App' env f es = format "({} {})" (smt2 env f, smt2many (smt2 env <$> es)) -- makeApplication env f es 



mkRel env Ne  e1 e2         = mkNe env e1 e2
mkRel env Une e1 e2         = mkNe env e1 e2
mkRel env r   e1 e2         = format "({} {} {})"      (smt2 env r , smt2 env e1, smt2 env e2)
mkNe  env e1 e2             = format "(not (= {} {}))" (smt2 env e1, smt2 env e2)

instance SMTLIB2 Command where
  -- NIKI TODO: formalize this transformation
  smt2 env (Declare x ts t)
     | isSMTSymbol x  
     = format "(declare-fun {} ({}) {})"  (smt2 env x, smt2s env ts, smt2 env t)
     | null ts && isSMTSort t
     = format "(declare-fun {} () {})"    (smt2 env x, smt2 env t)
     | otherwise
     = format "(declare-fun {} () {})"    (smt2 env x, smt2 env intSort)    

  smt2 env (Define t)          = format "(declare-sort {})"         (Only $ smt2 env t)
  smt2 env (Assert Nothing p)  = format "(assert {})"               (Only $ smt2 env p)
  smt2 env (Assert (Just i) p) = format "(assert (! {} :named p-{}))"  (smt2 env p, i)
  smt2 env (Distinct az)       = format "(assert (distinct {}))"    (Only $ smt2s env az)
  smt2 _   (Push)              = "(push 1)"
  smt2 _   (Pop)               = "(pop 1)"
  smt2 _   (CheckSat)          = "(check-sat)"
  smt2 env (GetValue xs)       = T.unwords $ ["(get-value ("] ++ fmap (smt2 env) xs ++ ["))"]

smt2s     :: SMTLIB2 a => SMTEnv -> [a] -> T.Text
smt2s env = smt2many . fmap (smt2 env)

smt2many :: [T.Text] -> T.Text
smt2many = T.intercalate " "


isSMTSymbol x = Thy.isTheorySymbol x || memberSEnv x initSMTEnv

{-
(declare-fun x () Int)
(declare-fun y () Int)
(assert (<= 0 x))
(assert (< x y))
(push 1)
(assert (not (<= 0 y)))
(check-sat)
(pop 1)
(push 1)
(assert (<= 0 y))
(check-sat)
(pop 1)
-}



-------------------------------------------------------------------------------------
----------------  Defunctionalizaion ------------------------------------------------
-------------------------------------------------------------------------------------

-- NIKI: This is new code, check and formalize!


-- make Application is called on uninterpreted functions 
-- 
-- makeApplication e [e1, ..., en] =  apply^n_s (e, toInt e1, ..., toInt en) 
-- where
-- applyn :: (Int, Int, ..., Int) -> s
-- e      :: (Int, ..., Int) -> s
-- toInt e = e, if e :: s, s is smt uninterpeted  
-- toInt e = s_to_Int (e), otherwise

-- s_to_Int :: s -> Int

makeApplication :: SMTEnv -> Expr -> [Expr] -> T.Text 
makeApplication env e es 
  = format "({} {})" (smt2 env f, smt2many ds) 
  where 
    f  = makeFunSymbol env e $ length es
    ds = smt2 env e:(toInt env <$> es)


makeFunSymbol :: SMTEnv -> Expr -> Int -> Symbol 
makeFunSymbol env e i 
  |  (FApp (FTC c) _)         <- s, fTyconSymbol c == "Set_Set" 
  = setApplyName i
  | (FApp (FApp (FTC c) _) _) <- s, fTyconSymbol c == "Map_t"   
  = mapApplyName i 
  | (FApp (FTC bv) (FTC s))   <- s, Thy.isBv bv, Just _ <- Thy.sizeBv s 
  = bitVecApplyName i
  | FTC c                     <- s, c == boolFTyCon 
  = boolApplyName i
  | FTC c                     <- s, c == realFTyCon 
  = realApplyName i 
  | otherwise
  = intApplyName i 
  where
    s = dropArgs i $ sortExpr dummySpan env e

    dropArgs 0 t           = t 
    dropArgs i (FAbs _ t)  = dropArgs i t 
    dropArgs i (FFunc _ t) = dropArgs (i-1) t 
    dropArgs _ _           = die $ err dummySpan "dropArgs: the impossible happened"

toInt ::  SMTEnv -> Expr -> T.Text 
toInt env e
  |  (FApp (FTC c) _)         <- s, fTyconSymbol c == "Set_Set" 
  = castWith env setToIntName e 
  | (FApp (FApp (FTC c) _) _) <- s, fTyconSymbol c == "Map_t"   
  = castWith env mapToIntName e 
  | (FApp (FTC bv) (FTC s))   <- s, Thy.isBv bv, Just _ <- Thy.sizeBv s 
  = castWith env bitVecToIntName e 
  | FTC c                     <- s, c == boolFTyCon 
  = castWith env boolToIntName e
  | FTC c                     <- s, c == realFTyCon 
  = castWith env realToIntName e
  | otherwise
  = smt2 env e 
  where
    s = sortExpr dummySpan env e

isSMTSort :: Sort -> Bool 
isSMTSort s
  | (FApp (FTC c) _)         <- s, fTyconSymbol c == "Set_Set" 
  = True
  | (FApp (FApp (FTC c) _) _) <- s, fTyconSymbol c == "Map_t"   
  = True
  | (FApp (FTC bv) (FTC s))   <- s, Thy.isBv bv, Just _ <- Thy.sizeBv s 
  = True
  | FTC c                     <- s, c == boolFTyCon 
  = True
  | FTC c                     <- s, c == realFTyCon 
  = True
  | otherwise
  = False      

     
castWith :: SMTEnv -> Symbol -> Expr -> T.Text 
castWith env s e = format "({} {})" (smt2 env s, smt2 env e)


setSort    = FApp (FTC $ symbolFTycon' "Set_Set") intSort
bitVecSort = FApp (FTC $ symbolFTycon' bitVecName) (FTC $ symbolFTycon' size32Name)
mapSort    = FApp (FApp (FTC $ symbolFTycon' "Map_t") intSort) intSort

symbolFTycon' = symbolFTycon . dummyLoc

initSMTEnv = fromListSEnv $ 
  [ (setToIntName,    FFunc setSort    intSort)
  , (bitVecToIntName, FFunc bitVecSort intSort)
  , (mapToIntName,    FFunc mapSort    intSort)
  , (boolToIntName,   FFunc boolSort   intSort)
  , (realToIntName,   FFunc realSort   intSort)
  ] 
  ++ concatMap makeApplies [1..7]

makeApplies i = 
  [ (intApplyName i,    go i intSort)
  , (setApplyName i,    go i setSort)
  , (bitVecApplyName i, go i bitVecSort)
  , (mapApplyName i,    go i mapSort)
  , (realApplyName i,   go i realSort)
  , (boolApplyName i,   go i boolSort)
  ]
  where
    go 0 s = FFunc intSort s
    go i s = FFunc intSort $ go (i-1) s

