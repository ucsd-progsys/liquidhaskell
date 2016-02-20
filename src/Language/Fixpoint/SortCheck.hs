{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE OverloadedStrings     #-}

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
  , sortExpr, checkSortExpr

  -- * Unify
  , unifyFast
  , unify

  -- * Apply Substitution
  , apply

  -- * Exported Sorts
  , boolSort
  , strSort
  , elaborate

  -- * Predicates on Sorts
  , isFirstOrder
  , isMono
  ) where


import           Control.Monad
import           Control.Monad.Except      (MonadError(..))
import qualified Data.HashMap.Strict       as M
import qualified Data.List                 as L
import           Data.Maybe                (mapMaybe, fromMaybe)

import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types hiding (subst)
import           Language.Fixpoint.Types.Visitor (foldSort)
import           Language.Fixpoint.Smt.Theories (theoryEnv)
import           Text.PrettyPrint.HughesPJ
import           Text.Printf

-- import Debug.Trace

-------------------------------------------------------------------------
-- | Predicates on Sorts ------------------------------------------------
-------------------------------------------------------------------------

-------------------------------------------------------------------------
isFirstOrder :: Sort -> Bool
-------------------------------------------------------------------------
isFirstOrder (FAbs _ t)    = isFirstOrder t
isFirstOrder (FFunc s1 s2) = noFun s1 && isFirstOrder s2
isFirstOrder _             = True

noFun (FFunc _ _) = False
noFun (FAbs _ _)  = False
noFun _           = True

-------------------------------------------------------------------------
isMono :: Sort -> Bool
-------------------------------------------------------------------------
isMono             = null . foldSort fv []
  where
    fv vs (FVar i) = i : vs
    fv vs _        = vs

-------------------------------------------------------------------------
-- | Sort Inference       -----------------------------------------------
-------------------------------------------------------------------------

sortExpr :: SrcSpan -> SEnv Sort -> Expr -> Sort
sortExpr l γ e = case runCM0 $ checkExpr f e of
    Left msg -> die $ err l (d msg)
    Right s  -> s
  where
    f   = (`lookupSEnvWithDistance` γ)
    d m = vcat [ "sortExpr failed on expression:"
               , nest 4 (pprint e)
               , "with error:"
               , nest 4 (text m)]

checkSortExpr :: SEnv Sort -> Expr -> Maybe Sort
checkSortExpr γ e = case runCM0 $ checkExpr f e of
    Left _   -> Nothing
    Right s  -> Just s
  where
    f x  = case lookupSEnv x γ of
            Just z  -> Found z
            Nothing -> Alts []


elaborate :: SEnv Sort -> Expr -> Expr
elaborate γ e
  = case runCM0 $ elab f e of
      Left msg -> die $ err dummySpan (d msg)
      Right s  -> fst s
  where
    f   = (`lookupSEnvWithDistance` γ')
    γ'  = unionSEnv γ theoryEnv
    d m = vcat [ "elaborate failed on:"
               , nest 4 (pprint e)
               , "with error"
               , nest 4 (text m)    ]

-------------------------------------------------------------------------
-- | Checking Refinements -----------------------------------------------
-------------------------------------------------------------------------

-- | Types used throughout checker

type StateM = Int

newtype CheckM a = CM {runCM :: StateM -> (StateM, Either String a)}

type Env      = Symbol -> SESearch Sort

instance Monad CheckM where
  return x     = CM $ \i -> (i, Right x)
  (CM m) >>= f = CM $ \i -> case m i of
                             (j, Left s)  -> (j, Left s)
                             (j, Right x) -> runCM (f x) j


instance MonadError String CheckM where
  throwError s = CM $ \i -> (i, Left s)
  (CM m) `catchError` f = CM $ \i -> case m i of
                                      (j, Left s) -> runCM (f s) j
                                      (j, Right x) -> (j, Right x)

instance Functor CheckM where
  fmap f (CM m) = CM $ \i -> case m i of {(j, Left s) -> (j, Left s); (j, Right x) -> (j, Right $ f x)}

instance Applicative CheckM where
  pure x     = CM $ \i -> (i, Right x)
  (CM f) <*> (CM m) = CM $ \i -> case m i of
                             (j, Left s)  -> (j, Left s)
                             (_, Right x) -> case f i of
                                 (k, Left s)  -> (k, Left s)
                                 (k, Right g) -> (k, Right $ g x)

initCM = 42
runCM0 act = snd $ runCM act initCM

class Freshable a where
  fresh   :: CheckM a
  refresh :: a -> CheckM a
  refresh _ = fresh

instance Freshable Int where
  fresh = CM (\n -> (n+1, Right n))

instance Freshable [Int] where
  fresh   = mapM (const fresh) [0..]
  refresh = mapM refresh

-------------------------------------------------------------------------
-- | Checking Refinements -----------------------------------------------
-------------------------------------------------------------------------

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
  check γ e = do {checkExpr f e; return ()}
   where f =  (`lookupSEnvWithDistance` γ)

  checkSort γ s e = void $ checkExpr f (ECst e s)
    where
      f           =  (`lookupSEnvWithDistance` γ)

instance Checkable SortedReft where
  check γ (RR s (Reft (v, ra))) = check γ' ra
   where
     γ' = insertSEnv v s γ

-------------------------------------------------------------------------
-- | Checking Expressions -----------------------------------------------
-------------------------------------------------------------------------

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
checkExpr _ PGrad          = return boolSort

checkExpr f (PAll  bs e )  = checkExpr (addEnv f bs) e
checkExpr f (PExist bs e)  = checkExpr (addEnv f bs) e
checkExpr f (ELam (x,t) e) = FFunc t <$> checkExpr (addEnv f [(x,t)]) e
checkExpr _ (ETApp _ _)    = error "SortCheck.checkExpr: TODO: implement ETApp"
checkExpr _ (ETAbs _ _)    = error "SortCheck.checkExpr: TODO: implement ETAbs"

addEnv f bs x
  = case L.lookup x bs of
      Just s  -> Found s
      Nothing -> f x

--------------------------------------------------------------------------------
-- | Elaborate expressions with types to make polymorphic instantiation explicit.
--------------------------------------------------------------------------------
elab :: Env -> Expr -> CheckM (Expr, Sort)
--------------------------------------------------------------------------------
elab f e@(EBin o e1 e2) = do
  (e1', s1) <- elab f e1
  (e2', s2) <- elab f e2
  s         <- checkExpr f e
  return (EBin o (ECst e1' s1) (ECst e2' s2), s)

elab f (EApp e1@(EApp _ _) e2) = do
  (e1', _, e2', s2, s) <- elabEApp f e1 e2
  return (EApp e1' (ECst e2' s2), s)

elab f (EApp e1 e2) = do
  (e1', s1, e2', s2, s) <- elabEApp f e1 e2
  return (EApp (ECst e1' s1) (ECst e2' s2), s)

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

elab _ e@PGrad =
  return (e, boolSort)

elab f e@(EVar x) =
  (e,) <$> checkSym f x

elab f (ENeg e) = do
  (e', s) <- elab f e
  return (ENeg e', s)

elab f (EIte p e1 e2) = do
  (p', _)  <- elab f p
  (e1', _) <- elab f e1
  (e2', _) <- elab f e2
  s <- checkIte f p e1 e2
  return (EIte p' e1' e2', s)

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

elab f (PAtom Eq e1 e2) = do
  t1        <- checkExpr f e1
  t2        <- checkExpr f e2
  (t1',t2') <- unite f  t1 t2
  e1'       <- elabAs f t1' e1
  e2'       <- elabAs f t2' e2
  return (PAtom Eq e1' e2', boolSort)

elab f (PAtom r e1 e2) = do
  (e1', _) <- elab f e1
  (e2', _) <- elab f e2
  return (PAtom r e1' e2', boolSort)

elab f (PExist bs e) = do
  (e', s) <- elab (addEnv f bs) e
  return (PExist bs e', s)

elab f (PAll bs e) = do
  (e', s) <- elab (addEnv f bs) e
  return (PAll bs e', s)

elab f (ELam (x,t) e) = do
  (e', s) <- elab (addEnv f [(x,t)]) e
  return (ELam (x,t) (ECst e' s), FFunc t s)

elab _ (ETApp _ _) =
  error "SortCheck.elab: TODO: implement ETApp"
elab _ (ETAbs _ _) =
  error "SortCheck.elab: TODO: implement ETAbs"

elabAs :: Env -> Sort -> Expr -> CheckM Expr
elabAs f t e@(EApp {}) = elabAppAs f t g es where (g, es) = splitEApp e
elabAs f _ e           = fst <$> elab f e

elabAppAs :: Env -> Sort -> Expr -> [Expr] -> CheckM Expr
elabAppAs f t g es = do
  gT    <- generalize =<< checkExpr f g
  eTs   <- mapM (checkExpr f) es
  gTios <- sortFunction (length es) gT
  su    <- unifys f (snd gTios:fst gTios) (t:eTs)
  let tg = apply su gT 
  g'    <- elabAs f tg g
  let ts = apply su <$> eTs
  es'   <- zipWithM (elabAs f) ts es
  return $ eApps (ECst g' tg) (zipWith ECst es' ts)

elabEApp  :: Env -> Expr -> Expr -> CheckM (Expr, Sort, Expr, Sort, Sort)
elabEApp f e1 e2 = do
  (e1', s1) <- elab f e1
  (e2', s2) <- elab f e2
  s         <- elabAppSort f s1 s2
  return (e1', s1, e2', s2, s)

unite :: Env -> Sort -> Sort -> CheckM (Sort, Sort)
-- unite' f t1@(FObj l) t2@FInt = do
  -- checkNumeric f l
  -- return (t1, t2)
-- unite' f t1@FInt t2@(FObj l) = do
  -- checkNumeric f l
  -- return (t1, t2)
unite f t1 t2 = do
  su <- unifys f [t1] [t2]
  return (apply su t1, apply su t2)

-- | Helper for checking symbol occurrences
checkSym :: Env -> Symbol -> CheckM Sort
checkSym f x
  = case f x of
     Found s -> return s
     Alts xs -> throwError $ errUnboundAlts x xs

-- | Helper for checking if-then-else expressions
checkIte :: Env -> Expr -> Expr -> Expr -> CheckM Sort
checkIte f p e1 e2
  = do checkPred f p
       t1 <- checkExpr f e1
       t2 <- checkExpr f e2
       ((`apply` t1) <$> unifys f [t1] [t2]) `catchError` (\_ -> throwError $ errIte e1 e2 t1 t2)

-- | Helper for checking cast expressions
checkCst :: Env -> Sort -> Expr -> CheckM Sort
checkCst f t (EApp g e)
  = checkApp f (Just t) g e
checkCst f t e
  = do t' <- checkExpr f e
       ((`apply` t) <$> unifys f [t] [t']) `catchError` (\_ -> throwError $ errCast e t' t)

elabAppSort :: Env -> Sort -> Sort -> CheckM Sort
elabAppSort f s1 s2 =
  do s1' <- generalize s1
     case s1' of
        FFunc sx s -> do θ <- unifys f [sx] [s2]
                         return $ apply θ s
        _ -> errorstar "Foo"

checkApp :: Env -> Maybe Sort -> Expr -> Expr -> CheckM Sort
checkApp f to g es
  = snd <$> checkApp' f to g es

checkExprAs f t (EApp g e)
  = checkApp f (Just t) g e
checkExprAs f t e 
  = do t' <- checkExpr f e 
       θ  <- unifys f [t'] [t]
       return $ apply θ t

-- | Helper for checking uninterpreted function applications
checkApp' :: Env -> Maybe Sort -> Expr -> Expr -> CheckM (TVSubst, Sort)
checkApp' f to g' e
  = do gt           <- checkExpr f g
       gt'          <- generalize gt
       (its, ot)    <- sortFunction (length es) gt'
       ets          <- mapM (checkExpr f) es
       θ            <- unifys f its ets
       let t         = apply θ ot
       case to of
         Nothing    -> return (θ, t)
         Just t'    -> do θ' <- unifyMany f θ [t] [t']
                          let ts = apply θ' <$> ets 
                          _ <- zipWithM (checkExprAs f) ts es 
                          return (θ', apply θ' t)
  where
    (g, es) = splitEApp $ EApp g' e

-- | Helper for checking binary (numeric) operations
checkNeg :: Env -> Expr -> CheckM Sort
checkNeg f e = do
  t <- checkExpr f e
  case t of
   FReal    -> return FReal
   FInt     -> return FInt
   (FObj l) -> checkNumeric f l >> return t
   _        -> throwError $ printf "Operand has non-numeric type %s in %s"
                            (showFix t) (showFix e)

checkOp f e1 o e2
  = do t1 <- checkExpr f e1
       t2 <- checkExpr f e2
       checkOpTy f (EBin o e1 e2) t1 t2

checkOpTy _ _ FReal FReal
  = return FReal

checkOpTy _ _ FInt FInt
  = return FInt

checkOpTy f _ t@(FObj l) (FObj l')
  | l == l'
  = checkNumeric f l >> return t

checkOpTy _ e t t'
  = throwError $ errOp e t t'

checkFractional f l
  = do t <- checkSym f l
       unless (t == FFrac) (throwError $ errNonFractional l)
       return ()

checkNumeric f l
  = do t <- checkSym f l
       unless (t == FNum || t == FFrac) (throwError $ errNonNumeric l)
       return ()

-------------------------------------------------------------------------
-- | Checking Predicates ------------------------------------------------
-------------------------------------------------------------------------

checkPred                  :: Env -> Expr -> CheckM ()
checkPred f e = checkExpr f e >>= checkBoolSort e

checkBoolSort :: Expr -> Sort -> CheckM ()
checkBoolSort e s
 | s == boolSort = return ()
 | otherwise     = throwError $ errBoolSort e s

-- | Checking Relations
checkRel :: Env -> Brel -> Expr -> Expr -> CheckM ()
checkRel f Eq e1 e2                = do t1 <- checkExpr f e1
                                        t2 <- checkExpr f e2
                                        su <- unifys f [t1] [t2]
                                        checkExprAs f (apply su t1) e1 
                                        checkExprAs f (apply su t2) e2
                                        checkRelTy f (PAtom Eq e1 e2) Eq t1 t2
checkRel f r  e1 e2                = do t1 <- checkExpr f e1
                                        t2 <- checkExpr f e2
                                        checkRelTy f (PAtom r e1 e2) r t1 t2

checkRelTy :: (Fixpoint a, PPrint a) => Env -> a -> Brel -> Sort -> Sort -> CheckM ()
checkRelTy f _ _ (FObj l) (FObj l') | l /= l'
  = (checkNumeric f l >> checkNumeric f l') `catchError` (\_ -> throwError $ errNonNumerics l l')
checkRelTy f _ _ FInt (FObj l)     = checkNumeric f l `catchError` (\_ -> throwError $ errNonNumeric l)
checkRelTy f _ _ (FObj l) FInt     = checkNumeric f l `catchError` (\_ -> throwError $ errNonNumeric l)
checkRelTy _ _ _ FReal FReal       = return ()
checkRelTy f _ _ FReal (FObj l)    = checkFractional f l `catchError` (\_ -> throwError $ errNonFractional l)
checkRelTy f _ _ (FObj l) FReal    = checkFractional f l `catchError` (\_ -> throwError $ errNonFractional l)

checkRelTy _ e Eq t1 t2
  | t1 == boolSort ||
    t2 == boolSort                 = throwError $ errRel e t1 t2
checkRelTy _ e Ne t1 t2
  | t1 == boolSort ||
    t2 == boolSort                 = throwError $ errRel e t1 t2
checkRelTy f _ Eq t1 t2            = void $ unifys f [t1] [t2]
checkRelTy f _ Ne t1 t2            = void $ unifys f [t1] [t2]

checkRelTy _ _ Ueq _ _             = return ()
checkRelTy _ _ Une _ _             = return ()
checkRelTy _ e _  t1 t2            = unless (t1 == t2)                 (throwError $ errRel e t1 t2)

-------------------------------------------------------------------------
-- | Sort Unification
-------------------------------------------------------------------------
unify :: Env -> Sort -> Sort -> Maybe TVSubst
-------------------------------------------------------------------------
unify f t1 t2
  = case runCM0 $ unify1 f emptySubst t1 t2 of
      Left _   -> Nothing
      Right su -> Just su


-------------------------------------------------------------------------
-- | Fast Unification; `unifyFast True` is just equality
-------------------------------------------------------------------------
unifyFast :: Bool -> Env -> Sort -> Sort -> Maybe TVSubst
-------------------------------------------------------------------------
unifyFast False f = unify f
unifyFast True  _ = uMono
  where
    uMono t1 t2
     | t1 == t2   = Just emptySubst
     | otherwise  = Nothing

-------------------------------------------------------------------------
unifys :: Env -> [Sort] -> [Sort] -> CheckM TVSubst
-------------------------------------------------------------------------
unifys f = unifyMany f emptySubst

unifyMany :: Env -> TVSubst -> [Sort] -> [Sort] -> CheckM TVSubst
unifyMany f θ ts ts'
  | length ts == length ts' = foldM (uncurry . unify1 f) θ $ zip ts ts'
  | otherwise               = throwError $ errUnifyMany ts ts'


unify1 :: Env -> TVSubst -> Sort -> Sort -> CheckM TVSubst
unify1 f θ (FVar i) t
  = unifyVar f θ i t
unify1 f θ t (FVar i)
  = unifyVar f θ i t
unify1 f θ (FApp t1 t2) (FApp t1' t2')
  = unifyMany f θ [t1, t2] [t1', t2']
unify1 _ θ (FTC l1) (FTC l2)
  | isListTC l1 && isListTC l2
  = return θ
unify1 f θ t1@(FAbs _ _) t2 = do
  t1'<- generalize t1
  unifyMany f θ [t1'] [t2]
unify1 f θ t1 t2@(FAbs _ _) = do
  t2' <- generalize t2
  unifyMany f θ [t1] [t2']

unify1 f θ (FObj l) FInt = do
  checkNumeric f l
  return θ

unify1 f θ FInt (FObj l) = do
  checkNumeric f l
  return θ

unify1 f θ (FFunc t1 t2) (FFunc t1' t2') = do 
  unifyMany f θ [t1, t2] [t1', t2']

unify1 _ θ t1 t2
  | t1 == t2
  = return θ
  | otherwise
  = throwError $ errUnify t1 t2

subst (j,tj) t@(FVar i)
  | i == j    = tj
  | otherwise = t
subst su (FApp t1 t2)  = FApp (subst su t1) (subst su t2)
subst _  (FTC l)       = FTC l
subst su (FFunc t1 t2) = FFunc (subst su t1) (subst su t2)
subst (j,tj) (FAbs i t)
  | i == j    = FAbs i t
  | otherwise = FAbs i $ subst (j,tj) t
subst _  s             = s


generalize :: Sort -> CheckM Sort
generalize (FAbs i t) = do
  v      <- refresh 0
  let sub = (i, FVar v)
  subst sub <$> generalize t
generalize t =
  return t

unifyVar :: Env -> TVSubst -> Int -> Sort -> CheckM TVSubst
unifyVar _ θ i t@(FVar j)
  = case lookupVar i θ of
      Just t'       -> if t == t' then return θ else return $ updateVar j t' θ
      Nothing       -> return $ updateVar i t θ

unifyVar f θ i t
  = case lookupVar i θ of
      Just (FVar j) -> return $ updateVar i t $ updateVar j t θ
      Just t'       -> if t == t' then return θ else unify1 f θ t t'
      Nothing       -> return $ updateVar i t θ

-------------------------------------------------------------------------
-- | Applying a Type Substitution ---------------------------------------
-------------------------------------------------------------------------
apply :: TVSubst -> Sort -> Sort
-------------------------------------------------------------------------
apply θ          = sortMap f
  where
    f t@(FVar i) = fromMaybe t (lookupVar i θ)
    f t          = t

-------------------------------------------------------------------------
sortMap :: (Sort -> Sort) -> Sort -> Sort
-------------------------------------------------------------------------
sortMap f (FAbs i t)    = FAbs i (sortMap f t)
sortMap f (FFunc t1 t2) = FFunc (sortMap f t1) (sortMap f t2)
sortMap f (FApp t1 t2)  = FApp  (sortMap f t1) (sortMap f t2)
sortMap f t             = f t

------------------------------------------------------------------------
-- | Deconstruct a function-sort ---------------------------------------
------------------------------------------------------------------------

sortFunction :: Int -> Sort -> CheckM ([Sort], Sort)
sortFunction i t
  = case functionSort t of
     Nothing          -> throwError $ errNonFunction i t
     Just (_, ts, t') -> if length ts < i 
                          then throwError $ errNonFunction i t
                          else let (its, ots) = splitAt i ts 
                               in return (its, foldl FFunc t' ots)

------------------------------------------------------------------------
-- | API for manipulating Sort Substitutions ---------------------------
------------------------------------------------------------------------

newtype TVSubst = Th (M.HashMap Int Sort) deriving (Show)

lookupVar :: Int -> TVSubst -> Maybe Sort
lookupVar i (Th m)   = M.lookup i m

updateVar :: Int -> Sort -> TVSubst -> TVSubst
updateVar i t (Th m) = Th (M.insert i t m)

emptySubst :: TVSubst
emptySubst = Th M.empty

-------------------------------------------------------------------------
-- | Error messages -----------------------------------------------------
-------------------------------------------------------------------------

errUnify t1 t2       = printf "Cannot unify %s with %s" (showpp t1) (showpp t2)

errUnifyMany ts ts'  = printf "Cannot unify types with different cardinalities %s and %s"
                         (showpp ts) (showpp ts')
errRel e t1 t2       = printf "Invalid Relation %s with operand types %s and %s"
                         (showpp e) (showpp t1) (showpp t2)
errOp e t t'
  | t == t'          = printf "Operands have non-numeric types %s in %s"
                         (showpp t) (showpp e)
  | otherwise        = printf "Operands have different types %s and %s in %s"
                         (showpp t) (showpp t') (showpp e)
errIte e1 e2 t1 t2   = printf "Mismatched branches in Ite: then %s : %s, else %s : %s"
                         (showpp e1) (showpp t1) (showpp e2) (showpp t2)
errCast e t' t       = printf "Cannot cast %s of sort %s to incompatible sort %s"
                         (showpp e) (showpp t') (showpp t)
errUnboundAlts x xs  = printf "Unbound Symbol %s\n Perhaps you meant: %s"
                        (showpp x)
                        (foldr1 (\w s -> w ++ ", " ++ s) (showpp <$> xs))
errNonFunction i t   = printf "Sort %s is not a function with at least %s arguments" (showpp t) (showpp i)
errNonNumeric  l     = printf "FObj sort %s is not numeric" (showpp l)
errNonNumerics l l'  = printf "FObj sort %s and %s are different and not numeric" (showpp l) (showpp l')
errNonFractional  l  = printf "FObj sort %s is not fractional" (showpp l)
errBoolSort     e s  = printf "Expressions %s should have bool sort, but has %s" (showpp e) (showpp s)
