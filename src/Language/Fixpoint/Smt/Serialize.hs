{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}

-- | This module contains the code for serializing Haskell values
--   into SMTLIB2 format, that is, the instances for the @SMTLIB2@
--   typeclass. We split it into a separate module as it depends on
--   Theories (see @smt2App@).

module Language.Fixpoint.Smt.Serialize where

import           Control.Applicative         ((<$>))
import           Language.Fixpoint.Types
import           Language.Fixpoint.Smt.Types
import qualified Language.Fixpoint.Smt.Theories as Thy
import qualified Data.Text                      as T
import           Data.Text.Format
import qualified Data.Text.Lazy                 as LT
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
  smt2 s@(FFunc _ _)           = error $ "smt2 FFunc: " ++ show s
  smt2 FInt                    = "Int"
  smt2 FReal                   = "Real"
  smt2 t
    | t == boolSort            = "Bool"
  smt2 t
    | Just d <- Thy.smt2Sort t = d
  smt2 _                       = "Int"

instance SMTLIB2 Symbol where
  smt2 s
    | Just t <- Thy.smt2Symbol s = LT.fromStrict t
  smt2 s                         = LT.fromStrict . encode . symbolText $ s

instance SMTLIB2 (Symbol, Sort) where
  smt2 (sym, t) = format "({} {})"  (smt2 sym, smt2 t)

-- FIXME: this is probably too slow.
-- RJ: Yes it is!
encode :: T.Text -> T.Text
encode t = {-# SCC "smt2-encode" #-}
  foldr (uncurry T.replace) t [("[", "ZM"), ("]", "ZN"), (":", "ZC")
                              ,("(", "ZL"), (")", "ZR"), (",", "ZT")
                              ,("|", "zb"), ("#", "zh"), ("\\","zr")
                              ,("z", "zz"), ("Z", "ZZ"), ("%","zv")
                              ,(" ", "_") , ("'", "ZT")
                              ]

instance SMTLIB2 SymConst where
  smt2 = smt2 . symbol

instance SMTLIB2 Constant where
  smt2 (I n)   = format "{}" (Only n)
  smt2 (R d)   = format "{}" (Only d)

instance SMTLIB2 LocSymbol where
  smt2 = smt2 . val

instance SMTLIB2 Bop where
  smt2 Plus  = "+"
  smt2 Minus = "-"
  smt2 Times = "*"
  smt2 Div   = "/"
  smt2 Mod   = "mod"

instance SMTLIB2 Brel where
  smt2 Eq    = "="
  smt2 Ueq   = "="
  smt2 Gt    = ">"
  smt2 Ge    = ">="
  smt2 Lt    = "<"
  smt2 Le    = "<="
  smt2 _     = error "SMTLIB2 Brel"

instance SMTLIB2 Expr where
  smt2 (ESym z)         = smt2 (symbol z)
  smt2 (ECon c)         = smt2 c
  smt2 (EVar x)         = smt2 x
--   smt2 (ELit x _)       = smt2 x
  smt2 (EApp f es)      = smt2App f es
  smt2 (ENeg e)         = format "(- {})"         (Only $ smt2 e)
  smt2 (EBin o e1 e2)   = format "({} {} {})"     (smt2 o, smt2 e1, smt2 e2)
  smt2 (EIte e1 e2 e3)  = format "(ite {} {} {})" (smt2 e1, smt2 e2, smt2 e3)
  smt2 (ECst e _)       = smt2 e
  smt2 e                = error  $ "TODO: SMTLIB2 Expr: " ++ show e

smt2App :: LocSymbol -> [Expr] -> LT.Text

smt2App f es = fromMaybe (smt2App' f ds) (Thy.smt2App f ds)
  where
   ds        = smt2 <$> es

smt2App' f [] = smt2 f
smt2App' f ds = format "({} {})" (smt2 f, smt2many ds)

instance SMTLIB2 Pred where
  smt2 (PTrue)          = "true"
  smt2 (PFalse)         = "false"
  smt2 (PAnd [])        = "true"
  smt2 (PAnd ps)        = format "(and {})"    (Only $ smt2s ps)
  smt2 (POr [])         = "false"
  smt2 (POr ps)         = format "(or  {})"    (Only $ smt2s ps)
  smt2 (PNot p)         = format "(not {})"    (Only $ smt2 p)
  smt2 (PImp p q)       = format "(=> {} {})"  (smt2 p, smt2 q)
  smt2 (PIff p q)       = format "(=  {} {})"  (smt2 p, smt2 q)
  smt2 (PExist bs p)    = format "(exists ({}) {})"  (smt2s bs, smt2 p)
  smt2 (PBexp e)        = smt2 e
  smt2 (PAtom r e1 e2)  = mkRel r e1 e2
  smt2 _                = error "smtlib2 Pred"


mkRel Ne  e1 e2         = mkNe e1 e2
mkRel Une e1 e2         = mkNe e1 e2
mkRel r   e1 e2         = format "({} {} {})"      (smt2 r, smt2 e1, smt2 e2)
mkNe  e1 e2             = format "(not (= {} {}))" (smt2 e1, smt2 e2)

instance SMTLIB2 Command where
  smt2 (Declare x ts t)    = format "(declare-fun {} ({}) {})"  (smt2 x, smt2s ts, smt2 t)
  smt2 (Define t)          = format "(declare-sort {})"         (Only $ smt2 t)
  smt2 (Assert Nothing p)  = format "(assert {})"               (Only $ smt2 p)
  smt2 (Assert (Just i) p) = format "(assert (! {} :named p-{}))"  (smt2 p, i)
  smt2 (Distinct az)       = format "(assert (distinct {}))"    (Only $ smt2s az)
  smt2 (Push)              = "(push 1)"
  smt2 (Pop)               = "(pop 1)"
  smt2 (CheckSat)          = "(check-sat)"
  smt2 (GetValue xs)       = LT.unwords $ ["(get-value ("] ++ fmap smt2 xs ++ ["))"]

smt2s    :: SMTLIB2 a => [a] -> LT.Text
smt2s    = smt2many . fmap smt2

smt2many :: [LT.Text] -> LT.Text
smt2many = LT.intercalate " "

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
