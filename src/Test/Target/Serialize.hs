{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Test.Target.Serialize where

import qualified Data.List as List
import Data.Maybe
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import Data.Text.Format

import Language.Fixpoint.Misc
import Language.Fixpoint.Smt.Interface (Command(..))
import qualified Language.Fixpoint.Smt.Theories as Thy
import Language.Fixpoint.Types

class SMTLIB2 a where
  smt2 :: a -> Builder

instance SMTLIB2 Sort where
  smt2 s@(FFunc _ _)           = errorstar $ "smt2 FFunc: " ++ show s
  smt2 FInt                    = "Int"
  smt2 FReal                   = "Real"
  smt2 t
    | t == boolSort            = "Bool"
  smt2 t
    | Just d <- Thy.smt2Sort t = d
  smt2 (FObj s)                = Builder.fromText $ symbolSafeText s
  smt2 _                       = "Int"


instance SMTLIB2 Symbol where
  smt2 s
    | Just t <- Thy.smt2Symbol s = t
  smt2 s                         = Builder.fromText $ symbolSafeText  s

instance SMTLIB2 (Symbol, Sort) where
  smt2 (sym, t) = build "({} {})" (smt2 sym, smt2 t)

instance SMTLIB2 SymConst where
  smt2   = smt2   . symbol

instance SMTLIB2 Constant where
  smt2 (I n)   = build "{}" (Only n)
  smt2 (R d)   = build "{}" (Only d)
  smt2 (L t _) = build "{}" (Only t) -- errorstar $ "Horrors, how to translate: " ++ show c

instance SMTLIB2 LocSymbol where
  smt2 = smt2 . val

instance SMTLIB2 Bop where
  smt2 Plus   = "+"
  smt2 Minus  = "-"
  smt2 Times  = "*"
  smt2 Div    = "/"
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

instance SMTLIB2 Expr where
  smt2 (ESym z)         = smt2 (symbol z)
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
  -- FIXME
  smt2  _e               = "true" -- errorstar ("smtlib2 Pred  " ++ show e)



smt2App :: Expr -> Builder
smt2App e = fromMaybe (build "({} {})" (smt2 f, smt2many (smt2 <$> es)))
                      (Thy.smt2App f (smt2 <$> es))
  where
    (f, es) = splitEApp e



mkRel :: (SMTLIB2 a, SMTLIB2 a1) => Brel -> a -> a1 -> Builder
mkRel Ne  e1 e2         = mkNe e1 e2
mkRel Une e1 e2         = mkNe e1 e2
mkRel r   e1 e2         = build "({} {} {})" (smt2 r, smt2 e1, smt2 e2)

mkNe :: (SMTLIB2 a, SMTLIB2 a1) => a -> a1 -> Builder
mkNe  e1 e2             = build "(not (= {} {}))" (smt2 e1, smt2 e2)

instance SMTLIB2 Command where
  smt2 (Declare x ts t)    = build "(declare-fun {} ({}) {})"     (smt2 x, smt2s ts, smt2 t)
  smt2 (Define t)          = build "(declare-sort {})"            (Only $ smt2 t)
  smt2 (Assert Nothing p)  = build "(assert {})"                  (Only $ smt2 p)
  smt2 (Assert (Just i) p) = build "(assert (! {} :named p-{}))"  (smt2 p, i)
  smt2 (Distinct az)       = build "(assert (distinct {}))"       (Only $ smt2s az)
  smt2 (Push)              = "(push 1)"
  smt2 (Pop)               = "(pop 1)"
  smt2 (CheckSat)          = "(check-sat)"
  smt2 (GetValue xs)       = mconcat . List.intersperse " "
                           $ ["(get-value ("] ++ fmap smt2 xs ++ ["))"]
  smt2 (CMany cmds)        = smt2many (smt2 <$> cmds)


smt2s    :: SMTLIB2 a => [a] -> Builder
smt2s as = smt2many (smt2 <$> as)

smt2many :: [Builder] -> Builder
smt2many = mconcat . List.intersperse " "
