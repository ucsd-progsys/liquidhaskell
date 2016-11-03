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
--import           Language.Fixpoint.Types.Names (mulFuncName, divFuncName)
import           Language.Fixpoint.Smt.Types
import qualified Language.Fixpoint.Smt.Theories as Thy
import           Data.Monoid
import qualified Data.Text.Lazy.Builder         as Builder
import           Data.Text.Format
import           Language.Fixpoint.Misc (errorstar)
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

instance SMTLIB2 Symbol where
  smt2 s
    | Just t <- Thy.smt2Symbol s = t
  smt2 s                         = Builder.fromText $ symbolSafeText  s

instance SMTLIB2 (Symbol, Sort) where
  smt2 (sym, t) = build "({} {})" (smt2 sym, smt2 t)

instance SMTLIB2 SymConst where
  smt2 (SL s)  = build "\"{}\"" (Only s)


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
  smt2 (PExist [] p)    = smt2 p
  smt2 (PExist bs p)    = build "(exists ({}) {})"  (smt2s bs, smt2 p)
  smt2 (PAll   [] p)    = smt2 p
  smt2 (PAll   bs p)    = build "(forall ({}) {})"  (smt2s bs, smt2 p)

  smt2 (PAtom r e1 e2)  = mkRel r e1 e2
  smt2 PGrad            = "true"
  smt2 (ELam (x, _) e)  = smt2Lam x e
  smt2  e               = errorstar ("smtlib2 Pred  " ++ show e)


smt2Lam :: Symbol -> Expr -> Builder.Builder
smt2Lam x e = build "({} {} {})" (smt2 lambdaName, smt2 x, smt2 e)

smt2App :: Expr -> Builder.Builder
smt2App e = fromMaybe (build "({} {})" (smt2 f, smt2s es)) $ Thy.smt2App (eliminate f) $ map smt2 es
  where
    (f, es) = splitEApp' e


splitEApp' :: Expr -> (Expr, [Expr])
splitEApp'            = go []
  where
    go acc (EApp f e) = go (e:acc) f
    go acc (ECst e _) = go acc e
    go acc e          = (e, acc)

eliminate :: Expr -> Expr
eliminate (ECst e _) = eliminate e
eliminate e          = e

mkRel :: Brel -> Expr -> Expr -> Builder.Builder
mkRel Ne  e1 e2 = mkNe e1 e2
mkRel Une e1 e2 = mkNe e1 e2
mkRel r   e1 e2 = build "({} {} {})" (smt2 r, smt2 e1, smt2 e2)

mkNe :: Expr -> Expr -> Builder.Builder
mkNe  e1 e2              = build "(not (= {} {}))" (smt2 e1, smt2 e2)

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


smt2s    :: SMTLIB2 a => [a] -> Builder.Builder
smt2s as = smt2many (map smt2 as)
{-# INLINE smt2s #-}

smt2many :: [Builder.Builder] -> Builder.Builder
smt2many []     = mempty
smt2many [b]    = b
smt2many (b:bs) = b <> mconcat [ " " <> b | b <- bs ]
{-# INLINE smt2many #-}


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


initSMTEnv :: SEnv Sort
initSMTEnv = fromListSEnv $
  [ (setToIntName,    FFunc (setSort intSort)   intSort)
  , (bitVecToIntName, FFunc bitVecSort intSort)
  , (mapToIntName,    FFunc (mapSort intSort intSort) intSort)
  , (boolToIntName,   FFunc boolSort   intSort)
  , (realToIntName,   FFunc realSort   intSort)
  , (lambdaName   ,   FFunc intSort (FFunc intSort intSort))
  ]
  ++ concatMap makeApplies [1..maxLamArg]
  ++ [(makeLamArg s i, s) | i <- [1..maxLamArg], s <- sorts]


-- THESE ARE DUPLICATED IN DEFUNCTIONALIZATION
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
  ]
  where
    go 0 s = FFunc intSort s
    go i s = FFunc intSort $ go (i-1) s