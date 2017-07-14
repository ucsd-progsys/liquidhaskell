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

module Language.Fixpoint.Smt.Serialize () where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Smt.Types
import qualified Language.Fixpoint.Smt.Theories as Thy
import           Data.Monoid
import qualified Data.Text.Lazy.Builder         as Builder
import           Data.Text.Format
import           Language.Fixpoint.Misc (errorstar)
import           Data.Maybe (fromMaybe)

-- instance SMTLIB2 Sort where
--   smt2 s@(FFunc _ _)           = errorstar $ "smt2 FFunc: " ++ showpp s
--   smt2 FInt                    = "Int"
--   smt2 FReal                   = "Real"
--   smt2 t
--     | t == boolSort            = "Bool"
--   smt2 t
--     | Just d <- Thy.smt2Sort t = d
--   smt2 _                       = "Int"

instance SMTLIB2 (Symbol, Sort) where
  smt2 env c@(sym, t) = build "({} {})" (smt2 env sym, smt2Sort c t)

smt2Sort :: (PPrint a) => a -> Sort -> Builder.Builder
smt2Sort msg = go
  where
    go s@(FFunc _ _)             = errorstar $ unwords ["smt2 FFunc:", showpp msg, showpp s]
    go FInt                      = "Int"
    go FReal                     = "Real"
    go t
      | t == boolSort            = "Bool"
    go t
      | Just d <- Thy.smt2Sort t = d
    go _                         = "Int"


instance SMTLIB2 Symbol where
  smt2 env s
    | Just t <- Thy.smt2Symbol env s = t
  smt2 _ s                           = Builder.fromText $ symbolSafeText  s

instance SMTLIB2 SymConst where
  smt2 env = smt2 env . symbol

instance SMTLIB2 Constant where
  smt2 _ (I n)   = build "{}" (Only n)
  smt2 _ (R d)   = build "{}" (Only d)
  smt2 _ (L t _) = build "{}" (Only t)

instance SMTLIB2 LocSymbol where
  smt2 env = smt2 env . val

instance SMTLIB2 Bop where
  smt2 _ Plus   = "+"
  smt2 _ Minus  = "-"
  smt2 _ Times  = Builder.fromText $ symbolSafeText mulFuncName
  smt2 _ Div    = Builder.fromText $ symbolSafeText divFuncName
  smt2 _ RTimes = "*"
  smt2 _ RDiv   = "/"
  smt2 _ Mod    = "mod"

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
  smt2 env (ESym z)         = smt2 env z
  smt2 env (ECon c)         = smt2 env c
  smt2 env (EVar x)         = smt2 env x
  smt2 env e@(EApp _ _)     = smt2App env e
  smt2 env (ENeg e)         = build "(- {})" (Only $ smt2 env e)
  smt2 env (EBin o e1 e2)   = build "({} {} {})" (smt2 env o, smt2 env e1, smt2 env e2)
  smt2 env (EIte e1 e2 e3)  = build "(ite {} {} {})" (smt2 env e1, smt2 env e2, smt2 env e3)
  smt2 env (ECst e _)       = smt2 env e
  smt2 _   (PTrue)          = "true"
  smt2 _   (PFalse)         = "false"
  smt2 _   (PAnd [])        = "true"
  smt2 env (PAnd ps)        = build "(and {})"   (Only $ smt2s env ps)
  smt2 _   (POr [])         = "false"
  smt2 env (POr ps)         = build "(or  {})"   (Only $ smt2s env ps)
  smt2 env (PNot p)         = build "(not {})"   (Only $ smt2  env p)
  smt2 env (PImp p q)       = build "(=> {} {})" (smt2 env p, smt2 env q)
  smt2 env (PIff p q)       = build "(= {} {})"  (smt2 env p, smt2 env q)
  smt2 env (PExist [] p)    = smt2 env p
  smt2 env (PExist bs p)    = build "(exists ({}) {})"  (smt2s env bs, smt2 env p)
  smt2 env (PAll   [] p)    = smt2 env p
  smt2 env (PAll   bs p)    = build "(forall ({}) {})"  (smt2s env bs, smt2 env p)

  smt2 env (PAtom r e1 e2)  = mkRel env r e1 e2
  smt2 env (ELam (x, _) e)  = smt2Lam env x e
  smt2 _   e                = errorstar ("smtlib2 Pred  " ++ show e)


smt2Lam :: SymEnv -> Symbol -> Expr -> Builder.Builder
smt2Lam env x e = build "({} {} {})" (smt2 env lambdaName, smt2 env x, smt2 env e)

smt2App :: SymEnv -> Expr -> Builder.Builder
smt2App env e = fromMaybe (build "({} {})" (smt2 env f, smt2s env es)) $ Thy.smt2App env (eliminate f) (smt2 env <$> es)
  where
    (f, es)   = splitEApp' e


splitEApp' :: Expr -> (Expr, [Expr])
splitEApp'            = go []
  where
    go acc (EApp f e) = go (e:acc) f
    go acc (ECst e _) = go acc e
    go acc e          = (e, acc)

eliminate :: Expr -> Expr
eliminate (ECst e _) = eliminate e
eliminate e          = e

mkRel :: SymEnv -> Brel -> Expr -> Expr -> Builder.Builder
mkRel env Ne  e1 e2 = mkNe env e1 e2
mkRel env Une e1 e2 = mkNe env e1 e2
mkRel env r   e1 e2 = build "({} {} {})" (smt2 env r, smt2 env e1, smt2 env e2)

mkNe :: SymEnv -> Expr -> Expr -> Builder.Builder
mkNe env e1 e2      = build "(not (= {} {}))" (smt2 env e1, smt2 env e2)

instance SMTLIB2 Command where
  smt2 env c@(Declare x ts t)  = build "(declare-fun {} ({}) {})"     (smt2 env x, smt2many (smt2Sort c <$> ts), smt2Sort c t)
  smt2 _   c@(Define t)        = build "(declare-sort {})"            (Only $ smt2Sort c t)
  smt2 env (Assert Nothing p)  = build "(assert {})"                  (Only $ smt2 env p)
  smt2 env (Assert (Just i) p) = build "(assert (! {} :named p-{}))"  (smt2 env p, i)
  smt2 env (Distinct az)
    | length az < 2            = ""
    | otherwise                = build "(assert (distinct {}))"       (Only $ smt2s env az)
  smt2 env (AssertAxiom t)     = build "(assert {})"                  (Only $ smt2  env t)
  smt2 _   (Push)              = "(push 1)"
  smt2 _   (Pop)               = "(pop 1)"
  smt2 _   (CheckSat)          = "(check-sat)"
  smt2 env (GetValue xs)       = "(get-value (" <> smt2s env xs <> "))"
  smt2 env (CMany cmds)        = smt2many (smt2 env <$> cmds)

instance SMTLIB2 (Triggered Expr) where
  smt2 env (TR NoTrigger e)       = smt2 env e
  smt2 env (TR _ (PExist [] p))   = smt2 env p
  smt2 env t@(TR _ (PExist bs p)) = build "(exists ({}) (! {} :pattern({})))"  (smt2s env bs, smt2 env p, smt2s env (makeTriggers t))
  smt2 env (TR _ (PAll   [] p))   = smt2 env p
  smt2 env t@(TR _ (PAll   bs p)) = build "(forall ({}) (! {} :pattern({})))"  (smt2s env bs, smt2 env p, smt2s env (makeTriggers t))
  smt2 env (TR _ e)               = smt2 env e


{-# INLINE smt2s #-}
smt2s    :: SMTLIB2 a => SymEnv -> [a] -> Builder.Builder
smt2s env as = smt2many (smt2 env <$> as)

{-# INLINE smt2many #-}
smt2many :: [Builder.Builder] -> Builder.Builder
smt2many []     = mempty
smt2many [b]    = b
smt2many (b:bs) = b <> mconcat [ " " <> b | b <- bs ]
