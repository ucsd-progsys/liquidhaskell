{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Test.Target.Serialize where

import Data.Maybe
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import Data.Text.Format

import Language.Fixpoint.Misc
import Language.Fixpoint.Smt.Interface (Command(..))
import qualified Language.Fixpoint.Smt.Theories as Thy
import Language.Fixpoint.Types

class SMTLIB2 a where
  smt2 :: a -> Text

instance SMTLIB2 Sort where
  smt2 s@(FFunc _ _)           = errorstar $ "smt2 FFunc: " ++ show s
  smt2 FInt                    = "Int"
  smt2 FReal                   = "Real"
  smt2 t
    | t == boolSort            = "Bool"
  smt2 t
    | Just d <- Thy.smt2Sort t = Text.fromStrict d
  smt2 (FObj s)                = Text.fromStrict $ symbolSafeText s
  smt2 _                       = "Int"


instance SMTLIB2 Symbol where
  smt2 s
    | Just t <- Thy.smt2Symbol s = Text.fromStrict t
  smt2 s                         = Text.fromStrict $ symbolSafeText  s

instance SMTLIB2 (Symbol, Sort) where
  smt2 (sym, t) = format "({} {})" (smt2 sym, smt2 t)

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
  smt2  _e               = "true" -- errorstar ("smtlib2 Pred  " ++ show e)



smt2App :: Expr -> Text
smt2App e = fromMaybe (format "({} {})" (smt2 f, smt2many (smt2 <$> es)))
                      (Text.fromStrict <$> Thy.smt2App f (Text.toStrict . smt2 <$> es))
  where
    (f, es) = splitEApp e



mkRel Ne  e1 e2         = mkNe e1 e2
mkRel Une e1 e2         = mkNe e1 e2
mkRel r   e1 e2         = format "({} {} {})" (smt2 r, smt2 e1, smt2 e2)
mkNe  e1 e2             = format "(not (= {} {}))" (smt2 e1, smt2 e2)

instance SMTLIB2 Command where
  smt2 (Declare x ts t)    = format "(declare-fun {} ({}) {})"     (smt2 x, smt2s ts, smt2 t)
  smt2 (Define t)          = format "(declare-sort {})"            (Only $ smt2 t)
  smt2 (Assert Nothing p)  = format "(assert {})"                  (Only $ smt2 p)
  smt2 (Assert (Just i) p) = format "(assert (! {} :named p-{}))"  (smt2 p, i)
  smt2 (Distinct az)       = format "(assert (distinct {}))"       (Only $ smt2s az)
  smt2 (Push)              = "(push 1)"
  smt2 (Pop)               = "(pop 1)"
  smt2 (CheckSat)          = "(check-sat)"
  smt2 (GetValue xs)       = Text.unwords $ ["(get-value ("] ++ fmap smt2 xs ++ ["))"]
  smt2 (CMany cmds)        = smt2many (smt2 <$> cmds)


smt2s    :: SMTLIB2 a => [a] -> Text
smt2s as = smt2many (smt2 <$> as)

smt2many :: [Text] -> Text
smt2many = Text.intercalate " "
