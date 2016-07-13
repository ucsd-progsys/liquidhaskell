{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DoAndIfThenElse      #-}
-- | This module contains the code for serializing Haskell values
--   into SMTLIB2 format, that is, the instances for the @SMTLIB2@
--   typeclass. We split it into a separate module as it depends on
--   Theories (see @smt2App@).

module Language.Fixpoint.Smt.Serialize
       ( initSMTEnv )
       where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Visitor hiding (mapSort)
--import           Language.Fixpoint.Types.Names (mulFuncName, divFuncName)
import           Language.Fixpoint.Smt.Types
import qualified Language.Fixpoint.Smt.Theories as Thy
import           Data.Monoid
import qualified Data.List                      as L
import qualified Data.Text.Lazy.Builder         as Builder
import           Data.Text.Format
import           Language.Fixpoint.Misc (errorstar)

import           Language.Fixpoint.SortCheck (elaborate, unifySorts, apply)

import           Control.Monad.State

import           Data.Maybe (fromMaybe)


import Text.PrettyPrint.HughesPJ (text)
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
    | isString t               = build "{}" (Only Thy.string)
  smt2 t
    | Just d <- Thy.smt2Sort t = d
  smt2 _                       = "Int"

  defunc = return . defuncSort

defuncSort :: Sort -> Sort
defuncSort (FAbs _ t)      = defuncSort t
defuncSort (FFunc _ _)     = intSort
defuncSort t | isString t  = strSort
defuncSort t | isSMTSort t = t
defuncSort _               = intSort


instance SMTLIB2 Symbol where
  smt2 s
    | Just t <- Thy.smt2Symbol s = t
  smt2 s                         = Builder.fromText $ symbolSafeText  s

instance SMTLIB2 (Symbol, Sort) where
  smt2 (sym, t) = build "({} {})" (smt2 sym, smt2 t)

  defunc (sym, t) = do bx <- defunc sym
                       bt <- defunc t
                       return $ (bx, bt)


instance SMTLIB2 SymConst where
  smt2 (SL s)  = build "\"{}\"" (Only s) -- smt2   . symbol

instance SMTLIB2 Constant where
  smt2 (I n)   = build "{}" (Only n)
  smt2 (R d)   = build "{}" (Only d)
  smt2 (L t _) = build "{}" (Only t) -- errorstar $ "Horrors, how to translate: " ++ show c

instance SMTLIB2 LocSymbol where
  smt2 = smt2 . val

instance SMTLIB2 Bop where
  smt2 Plus   = "+"
  smt2 Minus  = "-"
  smt2 Times  = Builder.fromText $ symbolSafeText mulFuncName
  smt2 Div    = Builder.fromText $ symbolSafeText divFuncName
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
  smt2 (ESym z)         = smt2 z
  smt2 (ECon c)         = smt2 c
  smt2 (EVar x)         = smt2 x
  smt2 e@(EApp _ _)     = smt2App e
  smt2 (ENeg e)         = build "(- {})" (Only $ smt2 e)
  smt2 (EBin o e1 e2)   = build "({} {} {})" (smt2 o, smt2 e1, smt2 e2)
  smt2 (EIte e1 e2 e3)  = build "(ite {} {} {})" (smt2 e1, smt2 e2, smt2 e3)
  smt2 (ECst e _)       = smt2 e
  smt2 (PTrue)          = "true"
  smt2 (PFalse)         = "false"
  smt2 (PAnd [])        = "true"
  smt2 (PAnd ps)        = build "(and {})"   (Only $ smt2s ps)
  smt2 (POr [])         = "false"
  smt2 (POr ps)         = build "(or  {})"   (Only $ smt2s ps)
  smt2 (PNot p)         = build "(not {})"   (Only $ smt2  p)
  smt2 (PImp p q)       = build "(=> {} {})" (smt2 p, smt2 q)
  smt2 (PIff p q)       = build "(= {} {})"  (smt2 p, smt2 q)
  smt2 (PExist bs p)    = build "(exists ({}) {})"  (smt2s bs, smt2 p)
  smt2 (PAll   bs p)    = build "(forall ({}) {})"  (smt2s bs, smt2 p)

  smt2 (PAtom r e1 e2)  = mkRel r e1 e2
  smt2 PGrad            = "true"
  smt2 (ELam (x, _) e)  = smt2Lam x e
  smt2  e               = errorstar ("smtlib2 Pred  " ++ show e)


-- new version
  defunc (ESym s)         = defuncESym s
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
  defunc (PAtom r e1 e2)  = do e1' <- defunc e1
                               e2' <- defunc e2
                               defuncPAtom r e1' e2'
  defunc PGrad            = return PGrad
  defunc (ELam x e)       = ELam x <$> defunc e
  defunc  e               = errorstar ("defunc Pred: " ++ show e)


defuncESym :: SymConst -> SMT2 Expr
defuncESym s = do 
    istr <- istring <$> get 
    if istr 
      then return $ ESym s 
      else return $ eVar s 
-- This is not defuncionalization, should not happen in defunc

defuncBop :: Bop -> Expr -> Expr -> SMT2 Expr
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

smt2Lam :: Symbol -> Expr -> Builder.Builder
smt2Lam x e = build "({} {} {})" (smt2 lambdaName, smt2 x, smt2 e)

smt2App :: Expr -> Builder.Builder
smt2App e = fromMaybe (build "({} {})" (smt2 f, smt2s es)) $ Thy.smt2App (eliminate f) $ map smt2 es
  where
    (f, es) = splitEApp e


defuncApp :: Expr -> SMT2 Expr
defuncApp e = case Thy.smt2App (eliminate f) (smt2 <$> es) of
                Just _ -> eApps f <$> mapM defunc es
                _      -> if stringLen es'
                           then defunc $ EApp (EVar Thy.strLen) (head es')  
                           else defuncApp' f' es'
  where
    (f, es)   = splitEApp' e
    (f', es') = splitEApp  e
    stringLen [e] = (isString $ exprSort e) && (f == EVar Thy.genLen)
    stringLen _   = False 

splitEApp' :: Expr -> (Expr, [Expr])
splitEApp'            = go []
  where
    go acc (EApp f e) = go (e:acc) f
    go acc (ECst e _) = go acc e
    go acc e          = (e, acc)

eliminate :: Expr -> Expr
eliminate (ECst e _) = eliminate e
eliminate e          = e

defuncApp' :: Expr -> [Expr] -> SMT2 Expr
defuncApp' f [] = defunc f
defuncApp' f es = makeApplication f es
-- smt2App' env f es = build "({} {})" (smt2 env f, smt2many (smt2 env <$> es)) -- makeApplication env f es

defuncPAtom :: Brel -> Expr -> Expr -> SMT2 Expr
defuncPAtom Eq e1 e2
  | isFun e1, isFun e2
  = mkFunEq e1 e2
defuncPAtom r e1 e2
  = return $ PAtom r e1 e2

mkRel :: Brel -> Expr -> Expr -> Builder.Builder
mkRel Ne  e1 e2 = mkNe e1 e2
mkRel Une e1 e2 = mkNe e1 e2
mkRel r   e1 e2 = build "({} {} {})" (smt2 r, smt2 e1, smt2 e2)

mkNe :: Expr -> Expr -> Builder.Builder
mkNe  e1 e2              = build "(not (= {} {}))" (smt2 e1, smt2 e2)

isFun :: Expr -> Bool
isFun e | FFunc _ _ <- exprSort e = True
        | otherwise               = False

mkFunEq :: Expr -> Expr -> SMT2 Expr
mkFunEq e1 e2
  = do fflag <- f_ext <$> get
       if fflag
        then return $ PAnd [PAll (zip xs (defuncSort <$> ss))
                             (PAtom Eq
                                (ECst (eApps (EVar f) (e1:es)) s)
                                (ECst (eApps (EVar f) (e2:es)) s))
                            , PAtom Eq e1 e2]
        else return $ PAtom Eq e1 e2
  where
    es      = zipWith (\x s -> ECst (EVar x) s) xs ss
    xs      = (\i -> symbol ("local_fun_arg" ++ show i)) <$> [1..length ss]
    (s, ss) = go [] $ exprSort e1

    go acc (FFunc s ss) = go (s:acc) ss
    go acc s            = (s, reverse acc)

    f  = makeFunSymbol e1 $ length xs

instance SMTLIB2 Command where
  -- NIKI TODO: formalize this transformation
  smt2 (Declare x ts t)    = build "(declare-fun {} ({}) {})"     (smt2 x, smt2s ts, smt2 t)
  smt2 (Define t)          = build "(declare-sort {})"            (Only $ smt2 t)
  smt2 (Assert Nothing p)  = build "(assert {})"                  (Only $ smt2 p)
  smt2 (Assert (Just i) p) = build "(assert (! {} :named p-{}))"  (smt2 p, i)
  smt2 (Distinct az)
    -- Distinct must have at least 2 arguments
    | length az < 2        = ""
    | otherwise            = build "(assert (distinct {}))"       (Only $ smt2s az)
  smt2 (Push)              = "(push 1)"
  smt2 (Pop)               = "(pop 1)"
  smt2 (CheckSat)          = "(check-sat)"
  smt2 (GetValue xs)       = "(get-value (" <> smt2s xs <> "))"
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
    = do env      <- smt2env <$> get
         (p', fs) <- grapLambdas $ elaborate env p
         dfs      <- mapM defineFun fs
         baxioms  <- makeBetaReductionAsserts p'
         p''      <- defunc p'
         return $ CMany ((Assert Nothing <$> baxioms) ++ concat dfs ++ [Assert Nothing p''])

  defunc (Assert (Just i) p)
    = do env <- smt2env <$> get
         (p', fs) <- grapLambdas $ elaborate env p
         dfs <- mapM defineFun fs
         baxioms  <- makeBetaReductionAsserts p'
         p'' <- defunc p'
         return $ CMany ((Assert Nothing <$> baxioms) ++ concat dfs ++ [Assert (Just i) p''])
--   smt2 env (Assert (Just i) p) = build "(assert (! {} :named p-{}))"  (smt2 env $ elaborate env p, i)
  defunc (Distinct az)       = Distinct <$> mapM defunc az
  defunc (Push)              = return Push
  defunc (Pop)               = return Pop
  defunc (CheckSat)          = return CheckSat
  defunc (GetValue xs)       = return $ GetValue xs
  defunc (CMany cmds)        = CMany <$> mapM defunc cmds

smt2s    :: SMTLIB2 a => [a] -> Builder.Builder
smt2s as = smt2many (map smt2 as)
{-# INLINE smt2s #-}

smt2many :: [Builder.Builder] -> Builder.Builder
smt2many []     = mempty
smt2many [b]    = b
smt2many (b:bs) = b <> mconcat [ " " <> b | b <- bs ]
{-# INLINE smt2many #-}

defineFun :: (Symbol, Expr) -> SMT2 [Command]
defineFun (f, ELam (x, t) (ECst e tr))
  = do decl   <- defunc $ Declare f (t:(snd <$> xts)) tr
       assert1 <- withExtendedEnv [(f, FFunc t tr)] $
                   defunc $ Assert Nothing (PAll ((x,t):xts)
                                  (PAtom Eq (mkApp (EApp (EVar f) (EVar x)) (fst <$> xts)) bd))
       g <- freshSym
       assert2 <- withExtendedEnv [(f, FFunc t tr)] $
                  withNoExtensionality $
                   defunc $ Assert Nothing
        (PAll [(g, FFunc t tr)]
          (PImp
        (PAll [(x,t)] (PAtom Eq (EApp (EVar f) (EVar x)) (EApp (EVar g) (EVar x))))
        (PAtom Eq (EVar f) (EVar g))))
       fflag <- f_ext <$> get
       if fflag
        then return [decl, assert1, assert2]
        else errorstar "defineFun on no extensionality flag and with function definition" --  return [decl]
  where
    go acc (ELam (x, t) e) = go ((x,t):acc) e
    go acc (ECst e _)      = go acc e
    go acc e               = (acc, e)
    (xts, bd)              = go [] e
    mkApp                  = L.foldl' (\e' x -> EApp e' (EVar x))
    -- mkApp e' []     = e'
    -- mkApp e' (x:xs) = mkApp (EApp e' (EVar x)) xs

defineFun  _
  = errorstar "die"

isSMTSymbol :: Symbol -> Bool
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



--------------------------------------------------------------------------------
-- | Defunctionalization -------------------------------------------------------
--------------------------------------------------------------------------------

normalizeLamsFromTo :: Int ->  Expr -> (Int, Expr)

normalizeLams :: Expr -> Expr
normalizeLams e = snd $ normalizeLamsFromTo 1 e

normalizeLamsFromTo i e = go e
  where
    go (ELam (y, sy) e) = let (i', e') = go e
                              y'      = makeLamArg sy i'
                          in (i'+1, ELam (y', sy) (e' `subst1` (y, EVar y')))
    go (EApp e1 e2)     = let (i1, e1') = go e1
                              (i2, e2') = go e2
                          in (max i1 i2, EApp e1' e2')
    go (ECst e s)       = mapSnd (`ECst` s) (go e)
    go e                = (i, e)

    mapSnd f (x, y) = (x, f y)


-- RJ: can't you use the Visitor instead of this?
grapLambdas :: Expr -> SMT2 (Expr, [(Symbol, Expr)])
grapLambdas = go []
  where
    go acc e@(ELam (x,s) bd) = do ext <- f_ext <$> get
                                  if ext then do
                                     f <- freshSym
                                     return (ECst (EVar f) (exprSort e),(f, e):acc)
                                  else do
                                     (bd', acc') <- go acc bd
                                     return (normalizeLams $ ELam (x, s) bd', acc')
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


makeBetaReductionAsserts :: Expr -> SMT2 [Expr]
makeBetaReductionAsserts e
  = do aFlag <- a_eq   <$> get
       bFlag <- b_eq   <$> get
       nFlag <- f_norm <$> get
       let as1 = if aFlag then fold lamVis  () [] e else []
       let as2 = if bFlag then fold betaVis () [] e else []
       let as3 = if nFlag then fold normVis () [] e else []
       mapM defunc (as1 ++ as2 ++ as3)
  where
    betaVis = (defaultVisitor :: Visitor [Expr] ()) {accExpr = go }
    go _ e@(EApp f ex)
      | ELam (x, _) bd <- uncst f
      = [mkEq e (bd `subst1` (x, ex))] -- :(go acc f ++ go acc ex)
    go _ _ = []

    uncst (ECst e _) = uncst e
    uncst e          = e


    lamVis = (defaultVisitor :: Visitor [Expr] ()) {accExpr = go' }
    go' _ ee@(ELam (x, s) e)
      -- optimization: do it for each lambda once
      --  notElem ee cxt
      = [mkEq ee ee' | (i, ee') <- map (\j -> normalizeLamsFromTo j (ELam (x, s) e)) [1..maxLamArg-1], i <= maxLamArg ]
    go' _ _ = []


    normVis = (defaultVisitor :: Visitor [Expr] ()) {accExpr = go'' }
    go'' _ ee@(ELam _ _)
      -- optimization: do it for each lambda once
      --  notElem ee cxt
      = [mkEq ee (normalizeLams $  normalForm ee)]
    go'' _ _ = []

    normalForm (ELam x e)
      = ELam x (normalForm e)
    normalForm (EApp f ex)
      | ELam (x, _) bd <- uncst f
      = bd `subst1` (x, normalForm ex)
    normalForm (EApp e1 e2)
      = EApp (normalForm e1) (normalForm e2)
    normalForm (ECst e s)
      = ECst (normalForm e) s
    normalForm e
      = e

    mkEq e1 e2
      | e1 == e2  = PTrue
      | otherwise = PAtom Eq e1 e2


makeApplication :: Expr -> [Expr] -> SMT2 Expr
makeApplication e es = defunc e >>= (`go` es)
  where
    go f []     = return f
    go f (e:es) = do df <- defunc $ makeFunSymbol f 1
                     de <- defunc e
                     let res = eApps (EVar df) [ECst f (exprSort f), de]
                     let s  = exprSort (EApp f de)
                     go ((`ECst` s) res) es


{-

-- Old application: without currying
makeApplication e es
  = do df  <- defunc f
       de  <- defunc e
       des <- mapM toInt es
       return $ eApps (EVar df) (de:des)
  where
    f  = makeFunSymbol e $ length es
-}

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
  | isString s 
  = strApplyName i 
  | otherwise
  = intApplyName i
  where
    s = dropArgs ("dropArgs " ++ show (i, e, exprSort e)) i $ exprSort e

dropArgs :: String -> Int -> Sort -> Sort
dropArgs _ 0 t           = t
dropArgs s j (FAbs _ t)  = dropArgs s j t
dropArgs s j (FFunc _ t) = dropArgs s (j-1) t
dropArgs str j s
  = die $ err dummySpan $ text (str ++ "  dropArgs: the impossible happened" ++ show (j, s))

{-
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

castWith :: Symbol -> Expr -> SMT2 Expr
castWith s e =
  do bs <- defunc s
     be <- defunc e
     return $ EApp (EVar bs) be

-}
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
  = isString s 


initSMTEnv :: SEnv Sort
initSMTEnv = fromListSEnv $
  [ (setToIntName,    FFunc (setSort intSort)   intSort)
  , (bitVecToIntName, FFunc bitVecSort intSort)
  , (mapToIntName,    FFunc (mapSort intSort intSort) intSort)
  , (boolToIntName,   FFunc boolSort   intSort)
  , (strToIntName,    FFunc strSort    intSort)
  , (realToIntName,   FFunc realSort   intSort)
  , (lambdaName   ,   FFunc intSort (FFunc intSort intSort))
  ]
  ++ concatMap makeApplies [1..maxLamArg]
  ++ [(makeLamArg s i, s) | i <- [1..maxLamArg], s <- sorts]

maxLamArg :: Int
maxLamArg = 7

sorts :: [Sort]
sorts = [intSort]

-- NIKI TODO: allow non integer lambda arguments
-- sorts = [setSort intSort, bitVecSort intSort, mapSort intSort intSort, boolSort, realSort, intSort]

makeLamArg :: Sort -> Int  -> Symbol
makeLamArg _ i = intArgName i

makeApplies :: Int -> [(Symbol, Sort)]
makeApplies i =
  [ (intApplyName i,    go i intSort)
  , (setApplyName i,    go i (setSort intSort))
  , (bitVecApplyName i, go i bitVecSort)
  , (mapApplyName i,    go i $ mapSort intSort intSort)
  , (realApplyName i,   go i realSort)
  , (boolApplyName i,   go i boolSort)
  , (strApplyName i,    go i strSort)
  ]
  where
    go 0 s = FFunc intSort s
    go i s = FFunc intSort $ go (i-1) s


exprSort :: Expr -> Sort
exprSort (ECst _ s)
  = s
exprSort (ELam (_,s) e)
  = FFunc s $ exprSort e
exprSort (EApp e ex) | FFunc sx s <- gen $ exprSort e
  = maybe s (`apply` s) $ unifySorts (exprSort ex) sx
  where
    gen (FAbs _ t) = gen t
    gen t          = t
exprSort e
  = errorstar ("\nexprSort on unexpected expressions" ++ show e)
