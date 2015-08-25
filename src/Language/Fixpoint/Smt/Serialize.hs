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
import           Language.Fixpoint.Smt.Types
import           Language.Fixpoint.Smt.Theories
import qualified Data.Text                as T
import           Data.Text.Format
import qualified Data.Text.Lazy           as LT

instance SMTLIB2 Sort where
  smt2 FInt         = "Int"
  smt2 t
    | t == boolSort = "Bool"
  -- smt2 (FApp t []) | t == intFTyCon = "Int"
  -- smt2 (FApp t []) | t == boolFTyCon = "Bool"
  smt2 (FApp t [FApp ts _,_]) | t == appFTyCon  && fTyconSymbol ts == "Set_Set" = "Set"
  -- smt2 (FObj s)    = smt2 s
  smt2 s@(FFunc _ _) = error $ "smt2 FFunc: " ++ show s
  smt2 _           = "Int"

instance SMTLIB2 Symbol where
  smt2 s | Just t <- smt2Theory s --  M.lookup s smt_set_funs
         = LT.fromStrict t
  smt2 s = LT.fromStrict . encode . symbolText $ s

-- FIXME: this is probably too slow
encode :: T.Text -> T.Text
encode t = {-# SCC "encode" #-}
  foldr (\(x,y) -> T.replace x y) t [("[", "ZM"), ("]", "ZN"), (":", "ZC")
                                    ,("(", "ZL"), (")", "ZR"), (",", "ZT")
                                    ,("|", "zb"), ("#", "zh"), ("\\","zr")
                                    ,("z", "zz"), ("Z", "ZZ"), ("%","zv")]

instance SMTLIB2 SymConst where
  -- smt2 (SL s) = LT.fromStrict s
  smt2 = smt2 . symbol -- encodeSymConst


instance SMTLIB2 Constant where
  smt2 (I n)   = format "{}" (Only n)
  smt2 (R d)   = format "{}" (Only d)
  -- smt2 (L t _) = t

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
  smt2 (ESym z)         = smt2 z
  smt2 (ECon c)         = smt2 c
  smt2 (EVar x)         = smt2 x
  smt2 (ELit x _)       = smt2 x
  smt2 (EApp f es)      = smt2App f es
  smt2 (ENeg e)         = format "(- {})"         (Only $ smt2 e)
  smt2 (EBin o e1 e2)   = format "({} {} {})"     (smt2 o, smt2 e1, smt2 e2)
  smt2 (EIte e1 e2 e3)  = format "(ite {} {} {})" (smt2 e1, smt2 e2, smt2 e3)
  smt2 (ECst e _)       = smt2 e
  smt2 e                = error  $ "TODO: SMTLIB2 Expr: " ++ show e

smt2App :: LocSymbol -> [Expr] -> LT.Text
smt2App f []            = smt2 f
smt2App f [e]
  | val f == setEmp     = format "(= {} {})"      (emp, smt2 e)
  | val f == setSng     = format "({} {} {})"     (add, emp, smt2 e)
smt2App f es            = format "({} {})"        (smt2 f, smt2s es)


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

smt2s :: SMTLIB2 a => [a] -> LT.Text
smt2s = LT.intercalate " " . fmap smt2


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
