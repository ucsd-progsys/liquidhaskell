{-# LANGUAGE CPP                  #-}
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

module Language.Fixpoint.Smt.Serialize (smt2SortMono) where

import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Types
import qualified Language.Fixpoint.Types.Visitor as Vis
import           Language.Fixpoint.Smt.Types
import qualified Language.Fixpoint.Smt.Theories as Thy
#if !MIN_VERSION_base(4,14,0)
import           Data.Semigroup                 (Semigroup (..))
#endif

import qualified Data.Text.Lazy.Builder         as Builder
-- import           Data.Text.Format
import           Language.Fixpoint.Misc (sortNub, errorstar)
import           Language.Fixpoint.Utils.Builder
-- import Debug.Trace (trace)

instance SMTLIB2 (Symbol, Sort) where
  smt2 env c@(sym, t) = -- build "({} {})" (smt2 env sym, smt2SortMono c env t)
                        parenSeqs [smt2 env sym, smt2SortMono c env t]

smt2SortMono, smt2SortPoly :: (PPrint a) => a -> SymEnv -> Sort -> Builder.Builder
smt2SortMono = smt2Sort False
smt2SortPoly = smt2Sort True

smt2Sort :: (PPrint a) => Bool -> a -> SymEnv -> Sort -> Builder.Builder
smt2Sort poly _ env t = smt2 env (Thy.sortSmtSort poly (seData env) t)

smt2data :: SymEnv -> [DataDecl] -> Builder.Builder
smt2data env = smt2data' env . map padDataDecl

smt2data' :: SymEnv -> [DataDecl] -> Builder.Builder
smt2data' env ds = seqs [ parens $ smt2many (smt2dataname env <$> ds)
                         , parens $ smt2many (smt2datactors env <$> ds)
                         ]

 
smt2dataname :: SymEnv -> DataDecl -> Builder.Builder
smt2dataname env (DDecl tc as _) = parenSeqs [name, n]
  where
    name  = smt2 env (symbol tc)
    n     = smt2 env as 


smt2datactors :: SymEnv -> DataDecl -> Builder.Builder
smt2datactors env (DDecl _ as cs) = parenSeqs ["par", parens tvars, parens ds]
  where
    tvars        = smt2many (smt2TV <$> [0..(as-1)])
    smt2TV       = smt2 env . SVar
    ds           = smt2many (smt2ctor env as <$> cs) 

smt2ctor :: SymEnv -> Int -> DataCtor -> Builder.Builder
smt2ctor env _  (DCtor c [])  = smt2 env c
smt2ctor env as (DCtor c fs)  = parenSeqs [smt2 env c, fields]
                                
  where
    fields                 = smt2many (smt2field env as <$> fs)

smt2field :: SymEnv -> Int -> DataField -> Builder.Builder
smt2field env as d@(DField x t) = parenSeqs [smt2 env x, smt2SortPoly d env $ mkPoly as t]

-- | SMTLIB/Z3 don't like "unused" type variables; they get pruned away and
--   cause wierd hassles. See tests/pos/adt_poly_dead.fq for an example.
--   'padDataDecl' adds a junk constructor that "uses" up all the tyvars just
--   to avoid this pruning problem.

padDataDecl :: DataDecl -> DataDecl
padDataDecl d@(DDecl tc n cs)
  | hasDead    = DDecl tc n (junkDataCtor tc n : cs)
  | otherwise  = d
  where
    hasDead    = length usedVars < n
    usedVars   = declUsedVars d

junkDataCtor :: FTycon -> Int -> DataCtor
junkDataCtor c n = DCtor (atLoc c junkc) [DField (junkFld i) (FVar i) | i <- [0..(n-1)]]
  where
    junkc        = suffixSymbol "junk" (symbol c)
    junkFld i    = atLoc c    (intSymbol junkc i)

declUsedVars :: DataDecl -> [Int]
declUsedVars = sortNub . Vis.foldDataDecl go []
  where
    go is (FVar i) = i : is
    go is _        = is

instance SMTLIB2 Symbol where
  smt2 env s
    | Just t <- Thy.smt2Symbol env s = t
  smt2 _ s                           = symbolBuilder s

instance SMTLIB2 Int where 
  smt2 _ = Builder.fromString . show 

instance SMTLIB2 LocSymbol where
  smt2 env = smt2 env . val

instance SMTLIB2 SymConst where
  smt2 env = smt2 env . symbol

instance SMTLIB2 Constant where
  smt2 _ (I n)   = bShow n
  smt2 _ (R d)   = bFloat d
  smt2 _ (L t _) = lbb t

instance SMTLIB2 Bop where
  smt2 _ Plus   = "+"
  smt2 _ Minus  = "-"
  smt2 _ Times  = symbolBuilder mulFuncName
  smt2 _ Div    = symbolBuilder divFuncName
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
  smt2 env (ENeg e)         = parenSeqs ["-", smt2 env e]
  smt2 env (EBin o e1 e2)   = parenSeqs [smt2 env o, smt2 env e1, smt2 env e2]
  smt2 env (EIte e1 e2 e3)  = parenSeqs ["ite", smt2 env e1, smt2 env e2, smt2 env e3]
  smt2 env (ECst e t)       = smt2Cast env e t
  smt2 _   PTrue            = "true"
  smt2 _   PFalse           = "false"
  smt2 _   (PAnd [])        = "true"
  smt2 env (PAnd ps)        = parenSeqs ["and", smt2s env ps]
  smt2 _   (POr [])         = "false"
  smt2 env (POr ps)         = parenSeqs ["or", smt2s env ps] 
  smt2 env (PNot p)         = parenSeqs ["not", smt2  env p]
  smt2 env (PImp p q)       = parenSeqs ["=>", smt2 env p, smt2 env q]
  smt2 env (PIff p q)       = parenSeqs ["=", smt2 env p, smt2 env q]
  smt2 env (PExist [] p)    = smt2 env p
  smt2 env (PExist bs p)    = parenSeqs ["exists", parens (smt2s env bs), smt2 env p]
  smt2 env (PAll   [] p)    = smt2 env p
  smt2 env (PAll   bs p)    = parenSeqs ["forall", parens (smt2s env bs), smt2 env p] 
  smt2 env (PAtom r e1 e2)  = mkRel env r e1 e2
  smt2 env (ELam b e)       = smt2Lam   env b e
  smt2 env (ECoerc t1 t2 e) = smt2Coerc env t1 t2 e
  smt2 _   e                = panic ("smtlib2 Pred  " ++ show e)



-- | smt2Cast uses the 'as x T' pattern needed for polymorphic ADT constructors
--   like Nil, see `tests/pos/adt_list_1.fq`

smt2Cast :: SymEnv -> Expr -> Sort -> Builder.Builder
smt2Cast env (EVar x) t = smt2Var env x t
smt2Cast env e        _ = smt2    env e

smt2Var :: SymEnv -> Symbol -> Sort -> Builder.Builder
smt2Var env x t
  | isLamArgSymbol x            = smtLamArg env x t
  | Just s <- symEnvSort x env
  , isPolyInst s t              = smt2VarAs env x t
  | otherwise                   = smt2 env x

smtLamArg :: SymEnv -> Symbol -> Sort -> Builder.Builder
smtLamArg env x t = symbolBuilder $ symbolAtName x env () (FFunc t FInt)

smt2VarAs :: SymEnv -> Symbol -> Sort -> Builder.Builder
smt2VarAs env x t = parenSeqs ["as", smt2 env x, smt2SortMono x env t]

smt2Lam :: SymEnv -> (Symbol, Sort) -> Expr -> Builder.Builder
smt2Lam env (x, xT) (ECst e eT) = parenSeqs [smt2 env lambda, x', smt2 env e]
  where
    x'                          = smtLamArg env x xT
    lambda                      = symbolAtName lambdaName env () (FFunc xT eT)

smt2Lam _ _ e
  = panic ("smtlib2: Cannot serialize unsorted lambda: " ++ showpp e)

smt2App :: SymEnv -> Expr -> Builder.Builder
smt2App env e@(EApp (EApp f e1) e2)
  | Just t <- unApplyAt f
  = parenSeqs [symbolBuilder (symbolAtName applyName env e t), smt2s env [e1, e2]]
smt2App env e
  | Just b <- Thy.smt2App smt2VarAs env f (smt2 env <$> es)
  = b
  | otherwise
  = parenSeqs [smt2 env f, smt2s env es]
  where
    (f, es)   = splitEApp' e

smt2Coerc :: SymEnv -> Sort -> Sort -> Expr -> Builder.Builder
smt2Coerc env t1 t2 e 
  | t1' == t2'  = smt2 env e
  | otherwise = parenSeqs [symbolBuilder coerceFn , smt2 env e]
  where 
    coerceFn  = symbolAtName coerceName env (ECoerc t1 t2 e) t
    t         = FFunc t1 t2
    t1'       = smt2SortMono e env t1 
    t2'       = smt2SortMono e env t2

splitEApp' :: Expr -> (Expr, [Expr])
splitEApp'            = go []
  where
    go acc (EApp f e) = go (e:acc) f
  --   go acc (ECst e _) = go acc e
    go acc e          = (e, acc)

mkRel :: SymEnv -> Brel -> Expr -> Expr -> Builder.Builder
mkRel env Ne  e1 e2 = mkNe env e1 e2
mkRel env Une e1 e2 = mkNe env e1 e2
mkRel env r   e1 e2 = parenSeqs [smt2 env r, smt2 env e1, smt2 env e2]

mkNe :: SymEnv -> Expr -> Expr -> Builder.Builder
mkNe env e1 e2      = key "not" (parenSeqs ["=",  smt2 env e1, smt2 env e2])

instance SMTLIB2 Command where
  smt2 env (DeclData ds)       = key "declare-datatypes" (smt2data env ds)
  smt2 env (Declare x ts t)    = parenSeqs ["declare-fun", smt2 env x, parens (smt2many (smt2 env <$> ts)), smt2 env t]
  smt2 env c@(Define t)        = key "declare-sort" (smt2SortMono c env t)
  smt2 env (Assert Nothing p)  = key "assert" (smt2 env p)
  smt2 env (Assert (Just i) p) = key "assert" (parens ("!"<+> smt2 env p <+> ":named p-" <> bShow i))
  smt2 env (Distinct az)
    | length az < 2            = ""
    | otherwise                = key "assert" (key "distinct" (smt2s env az))
  smt2 env (AssertAx t)        = key "assert" (smt2 env t)
  smt2 _   (Push)              = "(push 1)"
  smt2 _   (Pop)               = "(pop 1)"
  smt2 _   (CheckSat)          = "(check-sat)"
  smt2 env (GetValue xs)       = key "key-value" (parens (smt2s env xs))
  smt2 env (CMany cmds)        = smt2many (smt2 env <$> cmds)

instance SMTLIB2 (Triggered Expr) where
  smt2 env (TR NoTrigger e)       = smt2 env e
  smt2 env (TR _ (PExist [] p))   = smt2 env p
  smt2 env t@(TR _ (PExist bs p)) = smtTr env "exists" bs p t
  smt2 env (TR _ (PAll   [] p))   = smt2 env p
  smt2 env t@(TR _ (PAll   bs p)) = smtTr env "forall" bs p t
  smt2 env (TR _ e)               = smt2 env e
  
{-# INLINE smtTr #-}
smtTr :: SymEnv -> Builder.Builder -> [(Symbol, Sort)] -> Expr -> Triggered Expr -> Builder.Builder
smtTr env q bs p t = key q (parens (smt2s env bs) <+> key "!" (smt2 env p <+> ":pattern" <> parens (smt2s env (makeTriggers t)))) 

{-# INLINE smt2s #-}
smt2s    :: SMTLIB2 a => SymEnv -> [a] -> Builder.Builder
smt2s env as = smt2many (smt2 env <$> as)

{-# INLINE smt2many #-}
smt2many :: [Builder.Builder] -> Builder.Builder
smt2many = buildMany
