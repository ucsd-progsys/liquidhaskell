{-# LANGUAGE Strict                #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE BangPatterns          #-}

-- | This module has the functions that perform sort-checking, and related
-- operations on Fixpoint expressions and predicates.

module Language.Fixpoint.SortCheck  (
  -- * Sort Substitutions
    TVSubst
  , Env

  -- * Checking Well-Formedness
  , checkSorted
  , checkSortedReft
  , checkSortedReftFull
  , checkSortFull
  , pruneUnsortedReft

  -- * Sort inference
  , sortExpr
  , checkSortExpr
  , exprSort
  , exprSort_maybe

  -- * Unify
  , unifyFast
  , unifySorts

  -- * Apply Substitution
  , apply

  -- * Exported Sorts
  , boolSort
  , strSort

  -- * Sort-Directed Transformations
  , Elaborate (..)
  , applySorts
  , unApplyAt
  , toInt

  -- * Predicates on Sorts
  , isFirstOrder
  , isMono
  ) where

--  import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Except      -- (MonadError(..))
import           Control.Monad.State.Strict

import qualified Data.HashMap.Strict       as M
import qualified Data.List                 as L
import           Data.Maybe                (mapMaybe, fromMaybe, catMaybes)

import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types hiding   (subst)
import qualified Language.Fixpoint.Types.Visitor  as Vis
import qualified Language.Fixpoint.Smt.Theories   as Thy
-- import qualified Language.Fixpoint.Smt.Types      as Thy
import           Text.PrettyPrint.HughesPJ
import           Text.Printf

-- import Debug.Trace

--------------------------------------------------------------------------------
-- | Predicates on Sorts -------------------------------------------------------
--------------------------------------------------------------------------------
isMono :: Sort -> Bool
--------------------------------------------------------------------------------
isMono             = null . Vis.foldSort fv []
  where
    fv vs (FVar i) = i : vs
    fv vs _        = vs


--------------------------------------------------------------------------------
-- | Elaborate: make polymorphic instantiation explicit via casts,
--   make applications monomorphic for SMTLIB. This deals with
--   polymorphism by `elaborate`-ing all refinements except for
--   KVars. THIS IS NOW MANDATORY as sort-variables can be
--   instantiated to `int` and `bool`.
--------------------------------------------------------------------------------
class Elaborate a where
  elaborate :: String -> SymEnv -> a -> a

instance Elaborate (SInfo a) where
  elaborate x senv si = si
    { cm      = elaborate x senv <$> cm      si
    , bs      = elaborate x senv  $  bs      si
    , asserts = elaborate x senv <$> asserts si
    }

instance (Elaborate e) => (Elaborate (Triggered e)) where
  elaborate x env t = fmap (elaborate x env) t

instance (Elaborate a) => (Elaborate (Maybe a)) where
  elaborate x env t = fmap (elaborate x env) t

instance Elaborate Sort where
  elaborate _ _ = go
   where
      go s | isString s = strSort
      go (FAbs i s)    = FAbs i $ go s
      go (FFunc s1 s2) = funSort (go s1) (go s2)
      go (FApp s1 s2)  = FApp    (go s1) (go s2)
      go s             = s
      funSort :: Sort -> Sort -> Sort
      funSort = FApp . FApp funcSort

instance Elaborate Expr where
    elaborate msg env = elabNumeric . elabApply env . elabExpr msg env

instance Elaborate (Symbol, Sort) where
  elaborate msg env (x, s) = (x, elaborate msg env s)

instance Elaborate a => Elaborate [a]  where
  elaborate msg env xs = elaborate msg env <$> xs

elabNumeric :: Expr -> Expr
elabNumeric = Vis.mapExpr go
  where
    go (ETimes e1 e2)
      | exprSort "txn1" e1 == FReal
      , exprSort "txn2" e2 == FReal
      = ERTimes e1 e2
    go (EDiv   e1 e2)
      | exprSort ("txn3: " ++ showpp e1) e1 == FReal
      , exprSort "txn4" e2 == FReal
      = ERDiv   e1 e2
    go e
      = e

instance Elaborate SortedReft where
  elaborate x env (RR s (Reft (v, e))) = RR s (Reft (v, e'))
    where
      e'   = elaborate x env' e
      env' = insertSymEnv v s env

instance Elaborate BindEnv where
  elaborate z env = mapBindEnv (\i (x, sr) -> (x, elaborate (z ++ msg i x sr) env sr))
    where
      msg i x sr  = unwords [" elabBE",  show i, show x, show sr]

instance Elaborate (SimpC a) where
  elaborate x env c = c {_crhs = elaborate x env (_crhs c) }


--------------------------------------------------------------------------------
-- | 'elabExpr' adds "casts" to decorate polymorphic instantiation sites.
--------------------------------------------------------------------------------
elabExpr :: String -> SymEnv -> Expr -> Expr
elabExpr msg env e
  = case runCM0 $ elab (env, f) e of
      Left msg -> die $ err dummySpan (d msg)
      Right s  -> notracepp ("elabExpr: e =" ++ showpp e) $ fst s
    where
      sEnv = seSort env
      f    = (`lookupSEnvWithDistance` sEnv)
      -- γ'  = γ `mappend` (Thy.tsSort <$> Thy.theorySymbols)
      d m  = vcat [ "elaborate" <+> text msg <+> "failed on:"
                 , nest 4 (pprint e)
                 , "with error"
                 , nest 4 (text m)
                 , "in environment"
                 , nest 4 (pprint $ subEnv sEnv e)
                 ]

--------------------------------------------------------------------------------
-- | 'elabApply' replaces all direct function calls indirect calls via `apply`
--------------------------------------------------------------------------------
elabApply :: SymEnv -> Expr -> Expr
elabApply env = go
  where
    go e                  = case splitArgs e of
                             (e', []) -> step e'
                             (f , es) -> defuncEApp env (go f) (mapFst go <$> es)
    step (PAnd [])        = PTrue
    step (POr [])         = PFalse
    step (ENeg e)         = ENeg (go  e)
    step (EBin o e1 e2)   = EBin o (go e1) (go e2)
    step (EIte e1 e2 e3)  = EIte (go e1) (go e2) (go e3)
    step (ECst e t)       = ECst (go e) t
    step (PAnd ps)        = PAnd (go <$> ps)
    step (POr ps)         = POr  (go <$> ps)
    step (PNot p)         = PNot (go p)
    step (PImp p q)       = PImp (go p) (go q)
    step (PIff p q)       = PIff (go p) (go q)
    step (PExist bs p)    = PExist bs (go p)
    step (PAll   bs p)    = PAll   bs (go p)
    step (PAtom r e1 e2)  = PAtom r (go e1) (go e2)
    step e@(EApp {})      = go e
    step (ELam b e)       = ELam b       (go e)
    step (ECoerc a t e)   = ECoerc a t   (go e)
    step (PGrad k su i e) = PGrad k su i (go e)
    step e@(PKVar {})     = e
    step e@(ESym {})      = e
    step e@(ECon {})      = e
    step e@(EVar {})      = e
    -- ETApp, ETAbs, PAll, PExist
    step e                = error $ "TODO elabApply: " ++ showpp e

--------------------------------------------------------------------------------
-- | Sort Inference ------------------------------------------------------------
--------------------------------------------------------------------------------
sortExpr :: SrcSpan -> SEnv Sort -> Expr -> Sort
sortExpr l γ e = case runCM0 $ checkExpr f e of
    Left msg -> die $ err l (d msg)
    Right s  -> s
  where
    f   = (`lookupSEnvWithDistance` γ)
    d m = vcat [ "sortExpr failed on expression:"
               , nest 4 (pprint e)
               , "with error:"
               , nest 4 (text m)
               , "in environment"
               , nest 4 (pprint γ)
               ]

checkSortExpr :: SEnv Sort -> Expr -> Maybe Sort
checkSortExpr γ e = case runCM0 $ checkExpr f e of
    Left _   -> Nothing
    Right s  -> Just s
  where
    f x  = case lookupSEnv x γ of
            Just z  -> Found z
            Nothing -> Alts []

subEnv :: (Subable e) => SEnv a -> e -> SEnv a
subEnv g e = intersectWithSEnv (\t _ -> t) g g'
  where
    g' = fromListSEnv $ (, ()) <$> syms e


--------------------------------------------------------------------------------
-- | Checking Refinements ------------------------------------------------------
--------------------------------------------------------------------------------

-- | Types used throughout checker
type CheckM   = StateT ChState (Either ChError)
type ChError  = String
type ChState  = Int

type Env      = Symbol -> SESearch Sort
type ElabEnv  = (SymEnv, Env)

withError :: CheckM a -> String -> CheckM a
act `withError` e' = act `catchError` (\e -> throwError (e ++ "\n  because\n" ++ e'))

runCM0 :: CheckM a -> Either String a
runCM0 act = fst <$> runStateT act initCM
  where
    initCM = 42

fresh :: CheckM Int
fresh = do
  !n <- get
  put (n + 1)
  return n

--------------------------------------------------------------------------------
-- | Checking Refinements ------------------------------------------------------
--------------------------------------------------------------------------------
checkSortedReft :: SEnv SortedReft -> [Symbol] -> SortedReft -> Maybe Doc
checkSortedReft env xs sr = applyNonNull Nothing oops unknowns
  where
    oops                  = Just . (text "Unknown symbols:" <+>) . toFix
    unknowns              = [ x | x <- syms sr, x `notElem` v : xs, not (x `memberSEnv` env)]
    Reft (v,_)            = sr_reft sr

checkSortedReftFull :: Checkable a => SEnv SortedReft -> a -> Maybe Doc
checkSortedReftFull γ t
  = case runCM0 $ check γ' t of
      Left e  -> Just (text e)
      Right _ -> Nothing
    where
      γ' = sr_sort <$> γ

checkSortFull :: Checkable a => SEnv SortedReft -> Sort -> a -> Maybe Doc
checkSortFull γ s t
  = case runCM0 $ checkSort γ' s t of
      Left e  -> Just (text e)
      Right _ -> Nothing
    where
      γ' = sr_sort <$> γ

checkSorted :: Checkable a => SEnv Sort -> a -> Maybe Doc
checkSorted γ t
  = case runCM0 $ check γ t of
      Left e   -> Just (text e)
      Right _  -> Nothing

pruneUnsortedReft :: SEnv Sort -> SortedReft -> SortedReft
pruneUnsortedReft γ (RR s (Reft (v, p))) = RR s (Reft (v, tx p))
  where
    tx   = pAnd . mapMaybe (checkPred' f) . conjuncts
    f    = (`lookupSEnvWithDistance` γ')
    γ'   = insertSEnv v s γ
    -- wmsg t r = "WARNING: prune unsorted reft:\n" ++ showFix r ++ "\n" ++ t

checkPred' :: Env -> Expr -> Maybe Expr
checkPred' f p = res -- traceFix ("checkPred: p = " ++ showFix p) $ res
  where
    res        = case runCM0 $ checkPred f p of
                   Left _err   -> {- trace (_wmsg _err p) -} Nothing
                   Right _  -> Just p

class Checkable a where
  check     :: SEnv Sort -> a -> CheckM ()
  checkSort :: SEnv Sort -> Sort -> a -> CheckM ()

  checkSort γ _ = check γ

instance Checkable Expr where
  check γ e = void $ checkExpr f e
   where f =  (`lookupSEnvWithDistance` γ)

  checkSort γ s e = void $ checkExpr f (ECst e s)
    where
      f           =  (`lookupSEnvWithDistance` γ)

instance Checkable SortedReft where
  check γ (RR s (Reft (v, ra))) = check γ' ra
   where
     γ' = insertSEnv v s γ

--------------------------------------------------------------------------------
-- | Checking Expressions ------------------------------------------------------
--------------------------------------------------------------------------------
checkExpr                  :: Env -> Expr -> CheckM Sort
checkExpr _ (ESym _)       = return strSort
checkExpr _ (ECon (I _))   = return FInt
checkExpr _ (ECon (R _))   = return FReal
checkExpr _ (ECon (L _ s)) = return s
checkExpr f (EVar x)       = checkSym f x
checkExpr f (ENeg e)       = checkNeg f e
checkExpr f (EBin o e1 e2) = checkOp f e1 o e2
checkExpr f (EIte p e1 e2) = checkIte f p e1 e2
checkExpr f (ECst e t)     = checkCst f t e
checkExpr f (EApp g e)     = checkApp f Nothing g e
checkExpr f (PNot p)       = checkPred f p >> return boolSort
checkExpr f (PImp p p')    = mapM_ (checkPred f) [p, p'] >> return boolSort
checkExpr f (PIff p p')    = mapM_ (checkPred f) [p, p'] >> return boolSort
checkExpr f (PAnd ps)      = mapM_ (checkPred f) ps >> return boolSort
checkExpr f (POr ps)       = mapM_ (checkPred f) ps >> return boolSort
checkExpr f (PAtom r e e') = checkRel f r e e' >> return boolSort
checkExpr _ (PKVar {})     = return boolSort
checkExpr f (PGrad _ _ _ e)  = checkPred f e >> return boolSort

checkExpr f (PAll  bs e )  = checkExpr (addEnv f bs) e
checkExpr f (PExist bs e)  = checkExpr (addEnv f bs) e
checkExpr f (ELam (x,t) e) = FFunc t <$> checkExpr (addEnv f [(x,t)]) e
checkExpr f (ECoerc s t e) = checkExpr f (ECst e s) >> return t 
checkExpr _ (ETApp _ _)    = error "SortCheck.checkExpr: TODO: implement ETApp"
checkExpr _ (ETAbs _ _)    = error "SortCheck.checkExpr: TODO: implement ETAbs"

addEnv :: Eq a => (a -> SESearch b) -> [(a, b)] -> a -> SESearch b
addEnv f bs x
  = case L.lookup x bs of
      Just s  -> Found s
      Nothing -> f x

--------------------------------------------------------------------------------
-- | Elaborate expressions with types to make polymorphic instantiation explicit.
--------------------------------------------------------------------------------
elab :: ElabEnv -> Expr -> CheckM (Expr, Sort)
--------------------------------------------------------------------------------
elab f@(_, g) e@(EBin o e1 e2) = do
  (e1', s1) <- elab f e1
  (e2', s2) <- elab f e2
  s <- checkOpTy g e s1 s2
  return (EBin o (ECst e1' s1) (ECst e2' s2), s)

elab f (EApp e1@(EApp _ _) e2) = do
  (e1', _, e2', s2, s) <- notracepp "ELAB-EAPP" <$> elabEApp f e1 e2
  let e = eAppC s e1' (ECst e2' s2)
  let θ = unifyExpr (snd f) e
  return (applyExpr θ e, maybe s (`apply` s) θ)

elab f (EApp e1 e2) = do
  (e1', s1, e2', s2, s) <- elabEApp f e1 e2
  let e = eAppC s (ECst e1' s1) (ECst e2' s2)
  let θ = unifyExpr (snd f) e
  return (applyExpr θ e, maybe s (`apply` s) θ)

elab _ e@(ESym _) =
  return (e, strSort)

elab _ e@(ECon (I _)) =
  return (e, FInt)

elab _ e@(ECon (R _)) =
  return (e, FReal)

elab _ e@(ECon (L _ s)) =
  return (e, s)

elab _ e@(PKVar _ _) =
  return (e, boolSort)

elab f (PGrad k su i e) =
  ((, boolSort) . PGrad k su i . fst) <$> elab f e

elab (_, f) e@(EVar x) =
  (e,) <$> checkSym f x

elab f (ENeg e) = do
  (e', s) <- elab f e
  return (ENeg e', s)

elab f@(_,g) (EIte p e1 e2) = do
  (p', _)   <- elab f p
  (e1', s1) <- elab f e1
  (e2', s2) <- elab f e2
  s         <- checkIteTy g p e1' e2' s1 s2
  return (EIte p' (cast e1' s) (cast e2' s), s)

elab f (ECst e t) = do
  (e', _) <- elab f e
  return (ECst e' t, t)

elab f (PNot p) = do
  (e', _) <- elab f p
  return (PNot e', boolSort)

elab f (PImp p1 p2) = do
  (p1', _) <- elab f p1
  (p2', _) <- elab f p2
  return (PImp p1' p2', boolSort)

elab f (PIff p1 p2) = do
  (p1', _) <- elab f p1
  (p2', _) <- elab f p2
  return (PIff p1' p2', boolSort)

elab f (PAnd ps) = do
  ps' <- mapM (elab f) ps
  return (PAnd (fst <$> ps'), boolSort)

elab f (POr ps) = do
  ps' <- mapM (elab f) ps
  return (POr (fst <$> ps'), boolSort)

elab f@(_,g) e@(PAtom Eq e1 e2) = do
  t1        <- checkExpr g e1
  t2        <- checkExpr g e2
  (t1',t2') <- unite g e  t1 t2 `withError` (errElabExpr e)
  e1'       <- elabAs f t1' e1
  e2'       <- elabAs f t2' e2
  return (PAtom Eq (ECst e1' t1') (ECst e2' t2') , boolSort)

elab f (PAtom r e1 e2)
  | r == Ueq || r == Une = do
  (e1', _) <- elab f e1
  (e2', _) <- elab f e2
  return (PAtom r e1' e2', boolSort)

elab f@(env, _) (PAtom r e1 e2) = do
  e1' <- uncurry (toInt env) <$> elab f e1
  e2' <- uncurry (toInt env) <$> elab f e2
  return (PAtom r e1' e2', boolSort)

elab f (PExist bs e) = do
  (e', s) <- elab (elabAddEnv f bs) e
  let bs' = elaborate "PExist Args" mempty bs
  return (PExist bs' e', s)

elab f (PAll bs e) = do
  (e', s) <- elab (elabAddEnv f bs) e
  let bs' = elaborate "PAll Args" mempty bs
  return (PAll bs' e', s)

elab f (ELam (x,t) e) = do
  (e', s) <- elab (elabAddEnv f [(x, t)]) e
  let t' = elaborate "ELam Arg" mempty t
  return (ELam (x, t') (ECst e' s), FFunc t s)

elab f (ECoerc s t e) = do
  (e', _) <- elab f e
  return     (ECoerc s t e', t)

elab _ (ETApp _ _) =
  error "SortCheck.elab: TODO: implement ETApp"
elab _ (ETAbs _ _) =
  error "SortCheck.elab: TODO: implement ETAbs"

elabAddEnv :: Eq a => (t, a -> SESearch b) -> [(a, b)] -> (t, a -> SESearch b)
elabAddEnv (g, f) bs = (g, addEnv f bs)

cast :: Expr -> Sort -> Expr
cast (ECst e _) t = ECst e t
cast e          t = ECst e t

elabAs :: ElabEnv -> Sort -> Expr -> CheckM Expr
elabAs f t e = notracepp _msg <$>  go e
  where
    _msg  = "elabAs: t = " ++ showpp t ++ " e = " ++ showpp e
    go (EApp e1 e2)   = elabAppAs f t e1 e2
    -- go (EIte b e1 e2) = EIte b <$> go e1 <*> go e2
    go e              = fst    <$> elab f e

-- DUPLICATION with `checkApp'`
elabAppAs :: ElabEnv -> Sort -> Expr -> Expr -> CheckM Expr
elabAppAs env@(_, f) t g e = do
  gT       <- checkExpr f g
  eT       <- checkExpr f e
  (iT, oT, isu) <- checkFunSort gT
  let ge    = Just (EApp g e)
  su       <- unifyMany f ge isu [oT, iT] [t, eT]
  let tg    = apply su gT
  g'       <- elabAs env tg g
  let te    = apply su eT
  e'       <- elabAs env te e
  return    $ EApp (ECst g' tg) (ECst e' te)

elabEApp  :: ElabEnv -> Expr -> Expr -> CheckM (Expr, Sort, Expr, Sort, Sort)
elabEApp f@(_, g) e1 e2 = do
  (e1', s1)     <- notracepp ("elabEApp1: e1 = " ++ showpp e1) <$> elab f e1
  (e2', s2)     <- elab f e2
  (s1', s2', s) <- elabAppSort g e1 e2 s1 s2
  return           (e1', s1', e2', s2', s)

elabAppSort :: Env -> Expr -> Expr -> Sort -> Sort -> CheckM (Sort, Sort, Sort)
elabAppSort f e1 e2 s1 s2 = do
  let e            = Just (EApp e1 e2)
  (sIn, sOut, su) <- checkFunSort s1
  su'             <- unify1 f e su sIn s2
  return           $ (apply su' s1, apply su' s2, apply su' sOut)


--------------------------------------------------------------------------------
-- | defuncEApp monomorphizes function applications.
--------------------------------------------------------------------------------
defuncEApp :: SymEnv -> Expr -> [(Expr, Sort)] -> Expr
defuncEApp env e es = L.foldl' makeApplication e' es'
  where
    (e', es')       = takeArgs (seTheory env) e es

takeArgs :: SEnv TheorySymbol -> Expr -> [(Expr, a)] -> (Expr, [(Expr, a)])
takeArgs env e es =
  case Thy.isSmt2App env (Vis.stripCasts e) of
    Just n  -> let (es1, es2) = splitAt n es
               in (eApps e (fst <$> es1), es2)
    Nothing -> (e, es)

-- 'e1' is the function, 'e2' is the argument, 's' is the OUTPUT TYPE
makeApplication :: Expr -> (Expr, Sort) -> Expr
makeApplication e1 (e2, s) = ECst (EApp (EApp f e1) e2) s
  where
    f                      = applyAt (exprSort "makeAppl" e2) s

applyAt :: Sort -> Sort -> Expr
applyAt s t = ECst (EVar applyName) (FFunc s t)

-- JUST make "toInt" call "makeApplication" also, so they are wrapped in apply
-- MAY CAUSE CRASH (apply-on-apply) so rig `isSmt2App` to treat `apply` as SPECIAL.

-- TODO: proper toInt
toInt :: SymEnv -> Expr -> Sort -> Expr
toInt env e s
  | isSmtInt  = e
  | otherwise = ECst (EApp f (ECst e s)) FInt
  where
    isSmtInt  = isInt env s
    f         = toIntAt s

isInt :: SymEnv -> Sort -> Bool
isInt env s = case sortSmtSort False (seData env) s of
  SInt    -> True
  SString -> True
  SReal   -> True
  _       -> False

toIntAt :: Sort -> Expr
toIntAt s = ECst (EVar toIntName) (FFunc s FInt)

unApplyAt :: Expr -> Maybe Sort
unApplyAt (ECst (EVar f) t@(FFunc {}))
  | f == applyName = Just t
unApplyAt _        = Nothing


splitArgs :: Expr -> (Expr, [(Expr, Sort)])
splitArgs = go []
  where
    go acc (ECst (EApp e1 e) s) = go ((e, s) : acc) e1
    -- go acc e@(EApp f _)
    --    | Just _ <- unApplyAt f   = (e, acc)
    go _   e@EApp{}             = errorstar $ "UNEXPECTED: splitArgs: EApp without output type: " ++ showpp e
    -- go acc (ECst e _)           = go acc e
    go acc e                    = (e, acc)

--------------------------------------------------------------------------------
{- | [NOTE:apply-monomorphization]

     Because SMTLIB does not support higher-order functions,
     all _non-theory_ function applications

        EApp e1 e2

     are represented, in SMTLIB, as

        (Eapp (EApp apply e1) e2)

     where 'apply' is 'ECst (EVar "apply") t' and
           't'     is 'FFunc a b'
           'a','b' are the sorts of 'e2' and 'e1 e2' respectively.

     Note that *all polymorphism* goes through this machinery.

     Just before sending to the SMT solver, we use the cast 't'
     to generate a special 'apply_at_t' symbol.

     To let us do the above, we populate 'SymEnv' with the _set_
     of all sorts at which 'apply' is used, computed by 'applySorts'.
 -}

--------------------------------------------------------------------------------
applySorts :: Vis.Visitable t => t -> [Sort]
--------------------------------------------------------------------------------
applySorts = {- tracepp "applySorts" . -} (defs ++) . Vis.fold vis () []
  where
    defs   = [FFunc t1 t2 | t1 <- basicSorts, t2 <- basicSorts]
    vis    = (Vis.defaultVisitor :: Vis.Visitor [KVar] t) { Vis.accExpr = go }
    go _ (EApp (ECst (EVar f) t) _)
           | f == applyName
           = [t]
    go _ _ = []

--------------------------------------------------------------------------------
-- | Expressions sort  ---------------------------------------------------------
--------------------------------------------------------------------------------
exprSort :: String -> Expr -> Sort
exprSort msg e = fromMaybe (panic err) (exprSort_maybe e)
  where
    err        = printf "exprSort [%s] on unexpected expression %s" msg (show e)

  -- case exprSort_maybe e of
  --  Nothing -> errorstar ("\nexprSort [" ++ msg ++ "] on unexpected expressions " ++ show e)
  --  Just s  -> s


exprSort_maybe :: Expr -> Maybe Sort
exprSort_maybe = go
  where
    go (ECst _ s) = Just s
    go (ELam (_, sx) e) = FFunc sx <$> go e
    go (EApp e ex)
      | Just (FFunc sx s) <- genSort <$> go e
      = maybe s (`apply` s) <$> ((`unifySorts` sx) <$> go ex)
    go _ = Nothing

genSort :: Sort -> Sort
genSort (FAbs _ t) = genSort t
genSort t          = t

unite :: Env -> Expr -> Sort -> Sort -> CheckM (Sort, Sort)
unite f e t1 t2 = do
  su <- unifys f (Just e) [t1] [t2]
  return (apply su t1, apply su t2)


-- | Helper for checking symbol occurrences
checkSym :: Env -> Symbol -> CheckM Sort
checkSym f x = case f x of
  Found s -> instantiate s
  Alts xs -> throwError (errUnboundAlts x xs)

-- | Helper for checking if-then-else expressions
checkIte :: Env -> Expr -> Expr -> Expr -> CheckM Sort
checkIte f p e1 e2 = do
  checkPred f p
  t1 <- checkExpr f e1
  t2 <- checkExpr f e2
  checkIteTy f p e1 e2 t1 t2

checkIteTy :: Env -> Expr -> Expr -> Expr -> Sort -> Sort -> CheckM Sort
checkIteTy f p e1 e2 t1 t2
  = ((`apply` t1) <$> unifys f e' [t1] [t2]) `withError` (errIte e1 e2 t1 t2)
  where
    e' = Just (EIte p e1 e2)

-- | Helper for checking cast expressions
checkCst :: Env -> Sort -> Expr -> CheckM Sort
checkCst f t (EApp g e)
  = checkApp f (Just t) g e
checkCst f t e
  = do t' <- checkExpr f e
       ((`apply` t) <$> unifys f (Just e) [t] [t']) `withError` (errCast e t' t)

checkApp :: Env -> Maybe Sort -> Expr -> Expr -> CheckM Sort
checkApp f to g es
  = snd <$> checkApp' f to g es

checkExprAs :: Env -> Sort -> Expr -> CheckM Sort
checkExprAs f t (EApp g e)
  = checkApp f (Just t) g e
checkExprAs f t e
  = do t' <- checkExpr f e
       θ  <- unifys f (Just e) [t'] [t]
       return $ apply θ t

-- | Helper for checking uninterpreted function applications
-- | Checking function application should be curried, e.g.
-- | fromJust :: Maybe a -> a, f :: Maybe (b -> b), x: c |- fromJust f x
--   RJ: The above comment makes no sense to me :(

-- DUPLICATION with 'elabAppAs'
checkApp' :: Env -> Maybe Sort -> Expr -> Expr -> CheckM (TVSubst, Sort)
checkApp' f to g e = do
  gt       <- checkExpr f g
  et       <- checkExpr f e
  (it, ot, isu) <- checkFunSort gt
  let ge    = Just (EApp g e)
  su        <- unifyMany f ge isu [it] [et]
  let t     = apply su ot
  case to of
    Nothing    -> return (su, t)
    Just t'    -> do θ' <- unifyMany f ge su [t] [t']
                     let ti = apply θ' et
                     _ <- checkExprAs f ti e
                     return (θ', apply θ' t)


-- | Helper for checking binary (numeric) operations
checkNeg :: Env -> Expr -> CheckM Sort
checkNeg f e = do
  t <- checkExpr f e
  checkNumeric f t >> return t

checkOp :: Env -> Expr -> Bop -> Expr -> CheckM Sort
checkOp f e1 o e2
  = do t1 <- checkExpr f e1
       t2 <- checkExpr f e2
       checkOpTy f (EBin o e1 e2) t1 t2


checkOpTy :: Env -> Expr -> Sort -> Sort -> CheckM Sort
checkOpTy _ _ FInt FInt
  = return FInt

checkOpTy _ _ FReal FReal
  = return FReal
-- Coercing int to real is somewhat suspicious, but z3 seems
-- to be ok with it
checkOpTy _ _ FInt  FReal
  = return FReal
checkOpTy _ _ FReal FInt
  = return FReal

checkOpTy f _ t t'
  | t == t'
  = checkNumeric f t >> return t

checkOpTy _ e t t'
  = throwError $ errOp e t t'

checkFractional :: Env -> Sort -> CheckM ()
checkFractional f s@(FObj l)
  = do t <- checkSym f l
       unless (t == FFrac) (throwError $ errNonFractional s)
checkFractional _ s
  = unless (isReal s) (throwError $ errNonFractional s)

checkNumeric :: Env -> Sort -> CheckM ()
checkNumeric f s@(FObj l)
  = do t <- checkSym f l
       unless (t `elem` [FNum, FFrac, intSort, FInt]) (throwError $ errNonNumeric s)
checkNumeric _ s
  = unless (isNumeric s) (throwError $ errNonNumeric s)

checkEqConstr :: Env -> Maybe Expr -> a -> Symbol -> Sort -> CheckM a
checkEqConstr _ _  θ a (FObj b)
  | a == b
  = return θ
checkEqConstr f e θ a t = do
  case f a of
    Found tA -> do unless (tA == t) (throwError $ errUnify e tA t)
                   return θ
    _        -> throwError $ errUnify e (FObj a) t

--------------------------------------------------------------------------------
-- | Checking Predicates -------------------------------------------------------
--------------------------------------------------------------------------------
checkPred                  :: Env -> Expr -> CheckM ()
checkPred f e = checkExpr f e >>= checkBoolSort e

checkBoolSort :: Expr -> Sort -> CheckM ()
checkBoolSort e s
 | s == boolSort = return ()
 | otherwise     = throwError $ errBoolSort e s


-- | Checking Relations
checkRel :: Env -> Brel -> Expr -> Expr -> CheckM ()
checkRel f Eq e1 e2 = do
  t1 <- checkExpr f e1
  t2 <- checkExpr f e2
  su <- (unifys f (Just e) [t1] [t2]) `withError` (errRel e t1 t2)
  _  <- checkExprAs f (apply su t1) e1
  _  <- checkExprAs f (apply su t2) e2
  checkRelTy f e Eq t1 t2
  where
    e = PAtom Eq e1 e2

checkRel f r  e1 e2 = do
  t1 <- checkExpr f e1
  t2 <- checkExpr f e2
  checkRelTy f (PAtom r e1 e2) r t1 t2


checkRelTy :: Env -> Expr -> Brel -> Sort -> Sort -> CheckM ()
checkRelTy _ _ Ueq _ _             = return ()
checkRelTy _ _ Une _ _             = return ()
checkRelTy f _ _ s1@(FObj l) s2@(FObj l') | l /= l'
  = (checkNumeric f s1 >> checkNumeric f s2) `withError` (errNonNumerics l l')
checkRelTy _ _ _ FReal FReal = return ()
checkRelTy _ _ _ FInt  FReal = return ()
checkRelTy _ _ _ FReal FInt  = return ()
checkRelTy f _ _ FInt  s2    = checkNumeric    f s2 `withError` (errNonNumeric s2)
checkRelTy f _ _ s1    FInt  = checkNumeric    f s1 `withError` (errNonNumeric s1)
checkRelTy f _ _ FReal s2    = checkFractional f s2 `withError` (errNonFractional s2)
checkRelTy f _ _ s1    FReal = checkFractional f s1 `withError` (errNonFractional s1)
checkRelTy f e Eq t1 t2      = void (unifys f (Just e) [t1] [t2] `withError` (errRel e t1 t2))
checkRelTy f e Ne t1 t2      = void (unifys f (Just e) [t1] [t2] `withError` (errRel e t1 t2))

checkRelTy _ e _  t1 t2      = unless (t1 == t2) (throwError $ errRel e t1 t2)



--------------------------------------------------------------------------------
-- | Sort Unification on Expressions
--------------------------------------------------------------------------------

unifyExpr :: Env -> Expr -> Maybe TVSubst
unifyExpr f (EApp e1 e2) = Just $ mconcat $ catMaybes [θ1, θ2, θ]
  where
   θ1 = unifyExpr f e1
   θ2 = unifyExpr f e2
   θ  = unifyExprApp f e1 e2
unifyExpr f (ECst e _)
  = unifyExpr f e
unifyExpr _ _
  = Nothing

unifyExprApp :: Env -> Expr -> Expr -> Maybe TVSubst
unifyExprApp f e1 e2 = do
  t1 <- getArg $ exprSort_maybe e1
  t2 <- exprSort_maybe e2
  unify f (Just $ EApp e1 e2) t1 t2
  where
    getArg (Just (FFunc t1 _)) = Just t1
    getArg _                   = Nothing


--------------------------------------------------------------------------------
-- | Sort Unification
--------------------------------------------------------------------------------
unify :: Env -> Maybe Expr -> Sort -> Sort -> Maybe TVSubst
--------------------------------------------------------------------------------
unify f e t1 t2
  = case runCM0 $ unify1 f e emptySubst t1 t2 of
      Left _   -> Nothing
      Right su -> Just su

--------------------------------------------------------------------------------
unifySorts :: Sort -> Sort -> Maybe TVSubst
--------------------------------------------------------------------------------
unifySorts   = unifyFast False emptyEnv
  where
    emptyEnv = const $ die $ err dummySpan "SortChecl: lookup in Empty Env "

--------------------------------------------------------------------------------
-- | Fast Unification; `unifyFast True` is just equality
--------------------------------------------------------------------------------
unifyFast :: Bool -> Env -> Sort -> Sort -> Maybe TVSubst
--------------------------------------------------------------------------------
unifyFast False f = unify f Nothing
unifyFast True  _ = uMono
  where
    uMono t1 t2
     | t1 == t2   = Just emptySubst
     | otherwise  = Nothing


--------------------------------------------------------------------------------
unifys :: Env -> Maybe Expr -> [Sort] -> [Sort] -> CheckM TVSubst
--------------------------------------------------------------------------------
unifys f e = unifyMany f e emptySubst

unifyMany :: Env -> Maybe Expr -> TVSubst -> [Sort] -> [Sort] -> CheckM TVSubst
unifyMany f e θ ts ts'
  | length ts == length ts' = foldM (uncurry . unify1 f e) θ $ zip ts ts'
  | otherwise               = throwError $ errUnifyMany ts ts'


unify1 :: Env -> Maybe Expr -> TVSubst -> Sort -> Sort -> CheckM TVSubst
unify1 f e !θ (FVar !i) !t
  = unifyVar f e θ i t
unify1 f e !θ !t (FVar !i)
  = unifyVar f e θ i t
unify1 f e !θ (FApp !t1 !t2) (FApp !t1' !t2')
  = unifyMany f e θ [t1, t2] [t1', t2']
unify1 _ _ !θ (FTC !l1) (FTC !l2)
  | isListTC l1 && isListTC l2
  = return θ
unify1 f e !θ !t1@(FAbs _ _) !t2 = do
  !t1' <- instantiate t1
  unifyMany f e θ [t1'] [t2]
unify1 f e !θ !t1 t2@(FAbs _ _) = do
  !t2' <- instantiate t2
  unifyMany f e θ [t1] [t2']
unify1 _ _ !θ !s1 !s2
  | isString s1, isString s2
  = return θ
unify1 _ _ !θ !FInt  !FReal = return θ

unify1 _ _ !θ !FReal !FInt  = return θ

unify1 f e !θ !t FInt = do
  checkNumeric f t `withError` (errUnify e t FInt)
  return θ

unify1 f e !θ !FInt !t = do
  checkNumeric f t `withError` (errUnify e FInt t)
  return θ

unify1 f e !θ (FFunc !t1 !t2) (FFunc !t1' !t2') = do
  unifyMany f e θ [t1, t2] [t1', t2']

unify1 f e θ (FObj a) !t =
  checkEqConstr f e θ a t

unify1 f e θ !t (FObj a) =
  checkEqConstr f e θ a t

unify1 _ e θ !t1 !t2
  | t1 == t2
  = return θ
  | otherwise
  = throwError $ errUnify e t1 t2


subst :: Int -> Sort -> Sort -> Sort
subst !j !tj !t@(FVar !i)
  | i == j                  = tj
  | otherwise               = t

subst !j !tj (FApp !t1 !t2)  = FApp t1' t2'
  where
    !t1'                    = subst j tj t1
    !t2'                    = subst j tj t2

-- subst _ _  !(FTC l)         = FTC l
subst !j !tj (FFunc !t1 !t2) = FFunc t1' t2'
  where
    !t1'                    = subst j tj $! t1
    !t2'                    = subst j tj $! t2

subst !j !tj (FAbs !i !t)
  | i == j                  = FAbs i t
  | otherwise               = FAbs i t'
  where
    !t'                     = subst j tj t

subst _  _   !s             = s

--------------------------------------------------------------------------------
instantiate :: Sort -> CheckM Sort
--------------------------------------------------------------------------------
instantiate !t = go t
  where
    go (FAbs !i !t) = do
      !t'    <- instantiate t
      !v     <- fresh
      return  $ subst i (FVar v) t'
    go !t =
      return t

unifyVar :: Env -> Maybe Expr -> TVSubst -> Int -> Sort -> CheckM TVSubst
unifyVar _ _ θ !i !t@(FVar !j)
  = case lookupVar i θ of
      Just !t'      -> if t == t' then return θ else return (updateVar j t' θ)
      Nothing       -> return (updateVar i t θ)

unifyVar f e θ !i !t
  = case lookupVar i θ of
      Just (FVar !j) -> return $ updateVar i t $ updateVar j t θ
      Just !t'       -> if t == t' then return θ else unify1 f e θ t t'
      Nothing        -> return (updateVar i t θ)

--------------------------------------------------------------------------------
-- | Applying a Type Substitution ----------------------------------------------
--------------------------------------------------------------------------------
apply :: TVSubst -> Sort -> Sort
--------------------------------------------------------------------------------
apply θ          = Vis.mapSort f
  where
    f t@(FVar i) = fromMaybe t (lookupVar i θ)
    f t          = t

applyExpr :: Maybe TVSubst -> Expr -> Expr
applyExpr Nothing e  = e
applyExpr (Just θ) e = Vis.mapExpr f e
  where
    f (ECst e s) = ECst e (apply θ s)
    f e          = e

--------------------------------------------------------------------------------
_applyCoercion :: Symbol -> Sort -> Sort -> Sort
--------------------------------------------------------------------------------
_applyCoercion a t = Vis.mapSort f
  where
    f (FObj b)
      | a == b    = t
    f s           = s


--------------------------------------------------------------------------------
-- | Deconstruct a function-sort -----------------------------------------------
--------------------------------------------------------------------------------
checkFunSort :: Sort -> CheckM (Sort, Sort, TVSubst)
checkFunSort (FAbs _ t)    = checkFunSort t
checkFunSort (FFunc t1 t2) = return (t1, t2, emptySubst)
checkFunSort (FVar i)      = do j <- fresh
                                k <- fresh
                                return (FVar j, FVar k, updateVar i (FFunc (FVar j) (FVar k)) emptySubst)
checkFunSort t             = throwError $ errNonFunction 1 t

--------------------------------------------------------------------------------
-- | API for manipulating Sort Substitutions -----------------------------------
--------------------------------------------------------------------------------

newtype TVSubst = Th (M.HashMap Int Sort) deriving (Show)

instance Monoid TVSubst where
  mempty                  = Th mempty
  mappend (Th s1) (Th s2) = Th (mappend s1 s2)

lookupVar :: Int -> TVSubst -> Maybe Sort
lookupVar i (Th m)   = M.lookup i m

updateVar :: Int -> Sort -> TVSubst -> TVSubst
updateVar !i !t (Th m) = Th (M.insert i t m)

emptySubst :: TVSubst
emptySubst = Th M.empty

--------------------------------------------------------------------------------
-- | Error messages ------------------------------------------------------------
--------------------------------------------------------------------------------

errElabExpr    :: Expr -> String
errElabExpr e  = printf "Elaborate fails on %s" (showpp e)

errUnify :: Maybe Expr -> Sort -> Sort -> String
errUnify eo t1 t2 = printf "Cannot unify %s with %s %s"
                      (showpp t1) (showpp t2) (errUnifyExpr eo)

errUnifyExpr :: Maybe Expr -> String
errUnifyExpr Nothing  = ""
errUnifyExpr (Just e) = "in expression: " ++ showpp e

errUnifyMany :: [Sort] -> [Sort] -> String
errUnifyMany ts ts'  = printf "Cannot unify types with different cardinalities %s and %s"
                         (showpp ts) (showpp ts')

errRel :: Expr -> Sort -> Sort -> String
errRel e t1 t2       = printf "Invalid Relation %s with operand types %s and %s"
                         (showpp e) (showpp t1) (showpp t2)

errOp :: Expr -> Sort -> Sort -> String
errOp e t t'
  | t == t'          = printf "Operands have non-numeric types %s in %s"
                         (showpp t) (showpp e)
  | otherwise        = printf "Operands have different types %s and %s in %s"
                         (showpp t) (showpp t') (showpp e)

errIte :: Expr -> Expr -> Sort -> Sort -> String
errIte e1 e2 t1 t2   = printf "Mismatched branches in Ite: then %s : %s, else %s : %s"
                         (showpp e1) (showpp t1) (showpp e2) (showpp t2)

errCast :: Expr -> Sort -> Sort -> String
errCast e t' t       = printf "Cannot cast %s of sort %s to incompatible sort %s"
                         (showpp e) (showpp t') (showpp t)

errUnboundAlts :: Symbol -> [Symbol] -> String
errUnboundAlts x xs  = printf "Unbound Symbol %s\n Perhaps you meant: %s"
                        (showpp x)
                        (foldr1 (\w s -> w ++ ", " ++ s) (showpp <$> xs))

errNonFunction :: Int -> Sort -> String
errNonFunction i t   = printf "The sort %s is not a function with at least %s arguments\n" (showpp t) (showpp i)

errNonNumeric :: Sort -> String
errNonNumeric  l     = printf "The sort %s is not numeric" (showpp l)

errNonNumerics :: Symbol -> Symbol -> String
errNonNumerics l l'  = printf "FObj sort %s and %s are different and not numeric" (showpp l) (showpp l')

errNonFractional :: Sort -> String
errNonFractional  l  = printf "The sort %s is not fractional" (showpp l)

errBoolSort :: Expr -> Sort -> String
errBoolSort     e s  = printf "Expressions %s should have bool sort, but has %s" (showpp e) (showpp s)
