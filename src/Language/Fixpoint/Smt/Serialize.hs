{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}

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
import           Language.Fixpoint.Misc (errorstar) -- , traceShow)

import           Language.Fixpoint.SortCheck (elaborate)

import           Control.Monad.State
 
import           Data.Maybe (fromMaybe)


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
  smt2 s@(FFunc _ _)           = errorstar $ "smt2 FFunc: " ++ show s
  smt2 FInt                    = "Int"
  smt2 FReal                   = "Real"
  smt2 t
    | t == boolSort            = "Bool"
  smt2 t
    | Just d <- Thy.smt2Sort t = d
  smt2 _                       = "Int"

  defunc (FAbs _ t)      = defunc t
  defunc (FFunc _ _)     = return $ intSort
  defunc t | isSMTSort t = return t
  defunc _               = return intSort

instance SMTLIB2 Symbol where
  smt2 s
    | Just t <- Thy.smt2Symbol s = t
  smt2 s                         = symbolSafeText  s

instance SMTLIB2 (Symbol, Sort) where
  smt2 (sym, t) = format "({} {})" (smt2 sym, smt2 t)

  defunc (sym, t) = do bx <- defunc sym 
                       bt <- defunc t 
                       return $ (bx, bt)


instance SMTLIB2 SymConst where
  smt2   = smt2   . symbol


instance SMTLIB2 Constant where
  smt2 (I n)   = format "{}" (Only n)
  smt2 (R d)   = format "{}" (Only d)
  smt2 (L t _) = format "{}" (Only t) -- errorstar $ "Horrors, how to translate: " ++ show c

instance SMTLIB2 LocSymbol where
  smt2 = smt2 . val

instance SMTLIB2 Bop where
  smt2 Plus   = "+"
  smt2 Minus  = "-"
  smt2 Times  = symbolSafeText mulFuncName
  smt2 Div    = symbolSafeText divFuncName
  smt2 RTimes = "*"
  smt2 RDiv   = "/"
  smt2 Mod    = "mod"

instance SMTLIB2 Brel where
  smt2 Eq    = "="
  smt2 Ueq   = "="
  smt2 Gt    = ">"
  smt2 Ge    = ">="
  smt2 Lt    = "<"
  smt2 Le    = "<="
  smt2 _     = errorstar "SMTLIB2 Brel"

-- NV TODO: change the way EApp is printed
instance SMTLIB2 Expr where
  smt2 (ESym z)         = smt2 (symbol z)
  smt2 (ECon c)         = smt2 c
  smt2 (EVar x)         = smt2 x
  smt2 e@(EApp _ _)     = smt2App e
  smt2 (ENeg e)         = format "(- {})" (Only $ smt2 e)
  smt2 (EBin o e1 e2)   = format "({} {} {})" (smt2 o, smt2 e1, smt2 e2)
  smt2 (EIte e1 e2 e3)  = format "(ite {} {} {})" (smt2 e1, smt2 e2, smt2 e3)
  smt2 (ECst e _)       = smt2 e
  smt2 (PTrue)          = "true"
  smt2 (PFalse)         = "false"
  smt2 (PAnd [])        = "true"
  smt2 (PAnd ps)        = format "(and {})"   (Only $ smt2s ps)
  smt2 (POr [])         = "false"
  smt2 (POr ps)         = format "(or  {})"   (Only $ smt2s ps)
  smt2 (PNot p)         = format "(not {})"   (Only $ smt2  p)
  smt2 (PImp p q)       = format "(=> {} {})" (smt2 p, smt2 q)
  smt2 (PIff p q)       = format "(= {} {})"  (smt2 p, smt2 q)
  smt2 (PExist bs p)    = format "(exists ({}) {})"  (smt2s bs, smt2 p)
  smt2 (PAll   bs p)    = format "(forall ({}) {})"  (smt2s bs, smt2 p)

  smt2 (PAtom r e1 e2)  = mkRel r e1 e2
  smt2 PGrad            = "true"
  smt2  e               = errorstar ("smtlib2 Pred  " ++ show e)


-- new version 
  defunc e@(ESym _)       = return e 
  defunc e@(ECon _)       = return e 
  defunc e@(EVar _)       = return e 
  defunc e@(EApp _ _)     = defuncApp e
  defunc (ENeg e)         = ENeg <$> defunc e 
  defunc (EBin o e1 e2)   = defuncBop o e1 e2
  defunc (EIte e1 e2 e3)  = do e1'   <- defunc e1 
                               e2'   <- defunc e2 
                               e3'   <- defunc e3 
                               return $ EIte e1' e2' e3'
  defunc (ECst e t)       = (`ECst` t) <$> defunc e
  defunc (PTrue)          = return PTrue
  defunc (PFalse)         = return PFalse
  defunc (PAnd [])        = return PTrue
  defunc (PAnd ps)        = PAnd <$> mapM defunc ps
  defunc (POr [])         = return PFalse
  defunc (POr ps)         = POr <$> mapM defunc ps
  defunc (PNot p)         = PNot <$> defunc  p
  defunc (PImp p q)       = PImp <$> defunc p <*> defunc q 
  defunc (PIff p q)       = PIff <$> defunc p <*> defunc q 
  defunc (PExist bs p)    = do bs' <- mapM defunc bs 
                               p'  <- withExtendedEnv bs $ defunc p 
                               return $ PExist bs' p'
  defunc (PAll   bs p)    = do bs' <- mapM defunc bs 
                               p'  <- withExtendedEnv bs $ defunc p 
                               return $ PAll bs' p' 
  defunc (PAtom r e1 e2)  = PAtom r <$> defunc e1 <*> defunc e2 
  defunc PGrad            = return PGrad
  defunc  e               = errorstar ("smtlib2 Pred  " ++ show e)

defuncBop o e1 e2
  | o == Times, s1 == FReal, s2 == FReal
  = do e1' <- defunc e1 
       e2' <- defunc e2
       return $ EBin RTimes e1' e2'
  | o == Div, s1 == FReal, s2 == FReal
  = do e1' <- defunc e1
       e2' <- defunc e2
       return $ EBin RDiv e1' e2' 
  | otherwise
  = do e1' <- defunc e1 
       e2' <- defunc e2 
       return $ EBin o e1' e2' 
  where
    s1 = exprSort e1
    s2 = exprSort e2


smt2App :: Expr -> T.Text
smt2App e = fromMaybe (format "({} {})" (smt2 f, smt2many (smt2 <$> es))) (Thy.smt2App (eliminate f) $ (smt2 <$> es))
  where
    (f, es) = splitEApp e


defuncApp :: Expr -> SMT2 Expr 
defuncApp e = case Thy.smt2App (eliminate f) $ (smt2 <$> es) of 
                Just _ -> eApps f <$> mapM defunc es  
                _      -> defuncApp' f es
  where
    (f, es) = splitEApp e

eliminate (ECst e _) = e
eliminate e          = e

defuncApp' :: Expr -> [Expr] -> SMT2 Expr 
defuncApp' f [] = defunc f
defuncApp' f es = makeApplication f es
-- smt2App' env f es = format "({} {})" (smt2 env f, smt2many (smt2 env <$> es)) -- makeApplication env f es



mkRel Ne  e1 e2         = mkNe e1 e2
mkRel Une e1 e2         = mkNe e1 e2
mkRel r   e1 e2         = format "({} {} {})" (smt2 r, smt2 e1, smt2 e2)
mkNe  e1 e2             = format "(not (= {} {}))" (smt2 e1, smt2 e2)

instance SMTLIB2 Command where
  -- NIKI TODO: formalize this transformation
  smt2 (Declare x ts t)    = format "(declare-fun {} ({}) {})"     (smt2 x, smt2s ts, smt2 t)
  smt2 (Define t)          = format "(declare-sort {})"            (Only $ smt2 t)
  smt2 (Assert Nothing p)  = format "(assert {})"                  (Only $ smt2 p)
  smt2 (Assert (Just i) p) = format "(assert (! {} :named p-{}))"  (smt2 p, i)
  smt2 (Distinct az)       = format "(assert (distinct {}))"       (Only $ smt2s az)
  smt2 (Push)              = "(push 1)"
  smt2 (Pop)               = "(pop 1)"
  smt2 (CheckSat)          = "(check-sat)"
  smt2 (GetValue xs)       = T.unwords $ ["(get-value ("] ++ fmap smt2 xs ++ ["))"]
  smt2 (CMany cmds)        = smt2many (smt2 <$> cmds)


  defunc (Declare x ts t)
     | isSMTSymbol x
     = do dx  <- defunc x 
          dts <- mapM defunc ts
          dt  <- defunc t   
          return $ Declare dx dts dt 
     | null ts && isSMTSort t
     = do dx <- defunc x 
          dt <- defunc t
          return $ Declare dx [] dt 
     | otherwise
     = do dx <- defunc x 
          return $ Declare dx [] intSort

  defunc (Define t)  = return $ Define t 
  defunc (Assert Nothing p)  
    = do env <- smt2env <$> get 
         (p', fs) <- grapLambdas $ elaborate env p
         dfs <- mapM defineFun fs 
         p'' <- defunc p'
         return $ CMany (concat dfs ++ [Assert Nothing p''])

  defunc (Assert (Just i) p) 
    = do env <- smt2env <$> get 
         (p', fs) <- grapLambdas $ elaborate env p
         dfs <- mapM defineFun fs 
         p'' <- defunc p' 
         return $ CMany (concat dfs ++ [Assert (Just i) p''])
--   smt2 env (Assert (Just i) p) = format "(assert (! {} :named p-{}))"  (smt2 env $ elaborate env p, i)
  defunc (Distinct az)       = Distinct <$> mapM defunc az 
  defunc (Push)              = return Push 
  defunc (Pop)               = return Pop 
  defunc (CheckSat)          = return CheckSat
  defunc (GetValue xs)       = return $ GetValue xs 
  defunc (CMany cmds)        = CMany <$> mapM defunc cmds 

smt2s    :: SMTLIB2 a => [a] -> T.Text
smt2s as = smt2many (smt2 <$> as)

smt2many :: [T.Text] -> T.Text
smt2many = T.intercalate " "


defineFun :: (Symbol, Expr) -> SMT2 [Command]
defineFun (f, ELam (x, t) (ECst e tr))
  = do decl   <- defunc $ Declare f (t:(snd <$> xts)) tr 
       assert <- withExtendedEnv [(f, FFunc t tr)] $ 
                   defunc $ Assert Nothing (PAll ((x,t):xts) 
                                  (PAtom Eq (mkApp (EApp (EVar f) (EVar x)) (fst <$> xts)) bd))
       return $ [decl, assert]
  where
    go acc (ELam (x, t) e) = go ((x,t):acc) e 
    go acc (ECst e _)      = go acc e 
    go acc e               = (acc, e)
    
    (xts, bd) = go [] e 

    mkApp e' []     = e' 
    mkApp e' (x:xs) = mkApp (EApp e' (EVar x)) xs

defineFun  _ 
  = errorstar "die"


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

grapLambdas e = go [] e 
  where
    go acc e@(ELam _ _) = do f <- freshSym 
                             return (EVar f, (f, e):acc)
    go acc e@(ESym _)   = return (e, acc)
    go acc e@(ECon _)   = return (e, acc)
    go acc e@(EVar _)   = return (e, acc)
    go acc (EApp e1 e2) = do (e1', fs1) <- go [] e1 
                             (e2', fs2) <- go [] e2
                             return (EApp e1' e2', fs1 ++ fs2 ++ acc) 
    go acc (ENeg e)     = do (e', fs) <- go acc e 
                             return (ENeg e', fs)
    go acc (PNot e)     = do (e', fs) <- go acc e 
                             return (PNot e', fs)
    go acc (EBin b e1 e2) = do (e1', fs1) <- go [] e1 
                               (e2', fs2) <- go [] e2
                               return (EBin b e1' e2', fs1 ++ fs2 ++ acc) 
    go acc (PAtom b e1 e2) = do (e1', fs1) <- go [] e1 
                                (e2', fs2) <- go [] e2
                                return (PAtom b e1' e2', fs1 ++ fs2 ++ acc) 
    go acc (EIte e e1 e2) = do (e' , fs)  <- go [] e
                               (e1', fs1) <- go [] e1 
                               (e2', fs2) <- go [] e2
                               return (EIte e' e1' e2', fs ++ fs1 ++ fs2 ++ acc) 
    go acc (ECst e s)     = do (e', fs) <- go acc e
                               return (ECst e' s, fs)
    go acc (ETAbs e s)    = do (e', fs) <- go acc e 
                               return (ETAbs e' s, fs)
    go acc (ETApp e s)    = do (e', fs) <- go acc e 
                               return (ETApp e' s, fs)
    go acc (PAnd es)      = do es' <- mapM (go []) es
                               return (PAnd (fst <$> es'), concat (acc:(snd <$> es')))
    go acc (POr es)       = do es' <- mapM (go []) es
                               return (POr (fst <$> es'),  concat (acc:(snd <$> es')))
    go acc (PImp e1 e2)   = do (e1', fs1) <- go [] e1 
                               (e2', fs2) <- go [] e2
                               return (PImp e1' e2', fs1 ++ fs2 ++ acc) 
    go acc (PIff e1 e2)   = do (e1', fs1) <- go [] e1 
                               (e2', fs2) <- go [] e2
                               return (PIff e1' e2', fs1 ++ fs2 ++ acc) 
    go acc (PAll bs e)    = do (e', fs) <- go acc e 
                               return (PAll bs e', fs) 
    go acc (PExist bs e)  = do (e', fs) <- go acc e 
                               return (PExist bs e', fs) 
    go acc e@PGrad        = return (e, acc)
    go acc e@(PKVar _ _)  = return (e, acc)

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

makeApplication :: Expr -> [Expr] -> SMT2 Expr 
makeApplication e es
  = do df  <- defunc f 
       de  <- defunc e 
       des <- mapM toInt es 
       return $ eApps (EVar df) (de:des)
  where
    f  = makeFunSymbol e $ length es


makeFunSymbol :: Expr -> Int -> Symbol
makeFunSymbol e i
  | (FApp (FTC c) _)          <- s, fTyconSymbol c == "Set_Set"
  = setApplyName i
  | (FApp (FApp (FTC c) _) _) <- s, fTyconSymbol c == "Map_t"
  = mapApplyName i
  | (FApp (FTC bv) (FTC s))   <- s, Thy.isBv bv, Just _ <- Thy.sizeBv s
  = bitVecApplyName i
  | FTC c                     <- s, c == boolFTyCon
  = boolApplyName i
  | s == FReal
  = realApplyName i
  | otherwise
  = intApplyName i
  where
    s = dropArgs i $ exprSort e

    dropArgs 0 t           = t
    dropArgs i (FAbs _ t)  = dropArgs i t
    dropArgs i (FFunc _ t) = dropArgs (i-1) t
    dropArgs _ _           = die $ err dummySpan "dropArgs: the impossible happened"

toInt :: Expr -> SMT2 Expr 
toInt e
  |  (FApp (FTC c) _)         <- s, fTyconSymbol c == "Set_Set"
  = castWith setToIntName e
  | (FApp (FApp (FTC c) _) _) <- s, fTyconSymbol c == "Map_t"
  = castWith mapToIntName e
  | (FApp (FTC bv) (FTC s))   <- s, Thy.isBv bv, Just _ <- Thy.sizeBv s
  = castWith bitVecToIntName e
  | FTC c                     <- s, c == boolFTyCon
  = castWith boolToIntName e
  | FTC c                     <- s, c == realFTyCon
  = castWith realToIntName e
  | otherwise
  = defunc e
  where
    s = exprSort e

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
  | s == FReal
  = True
  | otherwise
  = False


castWith :: Symbol -> Expr -> SMT2 Expr 
castWith s e = 
  do bs <- defunc s 
     be <- defunc e
     return $ EApp (EVar bs) be

initSMTEnv = fromListSEnv $
  [ (setToIntName,    FFunc (setSort intSort)   intSort)
  , (bitVecToIntName, FFunc bitVecSort intSort)
  , (mapToIntName,    FFunc (mapSort intSort intSort) intSort)
  , (boolToIntName,   FFunc boolSort   intSort)
  , (realToIntName,   FFunc realSort   intSort)
  ]
  ++ concatMap makeApplies [1..7]

makeApplies i =
  [ (intApplyName i,    go i intSort)
  , (setApplyName i,    go i (setSort intSort))
  , (bitVecApplyName i, go i bitVecSort)
  , (mapApplyName i,    go i $ mapSort intSort intSort)
  , (realApplyName i,   go i realSort)
  , (boolApplyName i,   go i boolSort)
  ]
  where
    go 0 s = FFunc intSort s
    go i s = FFunc intSort $ go (i-1) s


exprSort :: Expr -> Sort
exprSort (ECst _ s) = s
exprSort e          = errorstar ("\nexprSort on unexpected expressions" ++ show e)
