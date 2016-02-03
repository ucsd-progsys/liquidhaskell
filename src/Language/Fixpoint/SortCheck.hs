{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module has the functions that perform sort-checking, and related
-- operations on Fixpoint expressions and predicates.

module Language.Fixpoint.SortCheck  (
  -- * Sort Substitutions
    TVSubst

  -- * Checking Well-Formedness
  , checkSorted
  , checkSortedReft
  , checkSortedReftFull
  , checkSortFull
  , pruneUnsortedReft

  -- * Unify
  , unify
  , unifyFast

  -- * Apply Substitution
  , apply

  -- * Exported Sorts
  , boolSort
  , strSort

  -- * Predicates on Sorts
  , isFirstOrder
  , isMono
  ) where


import           Control.Monad
import           Control.Monad.Except      (MonadError(..)) 
import qualified Data.HashMap.Strict       as M
import           Data.Maybe                (mapMaybe, fromMaybe)

import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types hiding (subst)
import           Language.Fixpoint.Types.Visitor (foldSort)

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

-- NUKE  fVars :: Sort -> [Int]
-- NUKE  fVars (FVar i)     = [i]
-- NUKE  fVars (FFunc _ ts) = concatMap fVars ts
-- NUKE  fVars (FApp t1 t2) = fVars t1 ++ fVars t2
-- NUKE  fVars _            = []

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
  fresh   = mapM (\_ -> fresh) [0..]
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
      Left err -> Just (text err)
      Right _  -> Nothing
    where
      γ' = sr_sort <$> γ

checkSortFull :: Checkable a => SEnv SortedReft -> Sort -> a -> Maybe Doc
checkSortFull γ s t
  = case runCM0 $ checkSort γ' s t of
      Left err -> Just (text err)
      Right _  -> Nothing
    where
      γ' = sr_sort <$> γ

checkSorted :: Checkable a => SEnv Sort -> a -> Maybe Doc
checkSorted γ t
  = case runCM0 $ check γ t of
      Left err -> Just (text err)
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
                   Left _   -> {- trace (_wmsg err p) -} Nothing
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

checkExpr _ (PAll _ _)     = error "SortCheck.checkExpr: TODO: implement PAll"
checkExpr _ (PExist _ _)   = error "SortCheck.checkExpr: TODO: implement PExist"

checkExpr _ (ETApp _ _)    = error "SortCheck.checkExpr: TODO: implement ETApp"
checkExpr _ (ETAbs _ _)    = error "SortCheck.checkExpr: TODO: implement ETAbs"

-- | Helper for checking symbol occurrences

checkSym f x
  = case f x of
     Found s -> return s
     Alts xs -> throwError $ errUnboundAlts x xs
--   $ traceFix ("checkSym: x = " ++ showFix x) (f x)

-- checkLocSym f x = checkSym f (val x)

-- | Helper for checking if-then-else expressions

checkIte f p e1 e2
  = do checkPred f p
       t1 <- checkExpr f e1
       t2 <- checkExpr f e2
       ((`apply` t1) <$> unifys [t1] [t2]) `catchError` (\_ -> throwError $ errIte e1 e2 t1 t2)

-- | Helper for checking cast expressions

checkCst f t (EApp g e)
  = checkApp f (Just t) g e
checkCst f t e
  = do t' <- checkExpr f e
       ((`apply` t) <$> unifys [t] [t']) `catchError` (\_ -> throwError $ errCast e t' t)


checkApp :: Env -> Maybe Sort -> Expr -> Expr -> CheckM Sort 
checkApp f to g es
  = snd <$> checkApp' f to g es

-- | Helper for checking uninterpreted function applications
checkApp' f to g' e
  = do gt           <- checkExpr f g
       gt'          <- generalize gt
       (_, its, ot) <- sortFunction gt'
       unless (length its == length es) $ throwError (errArgArity g its es (EApp g' e))
       ets          <- mapM (checkExpr f) es
       θ            <- unifys its ets
       let t         = apply θ ot
       case to of
         Nothing    -> return (θ, t)
         Just t'    -> do θ' <- unifyMany θ [t] [t']
                          return (θ', apply θ' t)
  where
    (g, es) = splitEApp $ EApp g' e

-- | Helper for checking binary (numeric) operations

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
       unless (t == FNum) (throwError $ errNonNumeric l)
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
checkRel :: (Symbol -> SESearch Sort) -> Brel -> Expr -> Expr -> CheckM ()
checkRel f Eq (EVar x) (EApp g es) = checkRelEqVar f x g es
checkRel f Eq (EApp g es) (EVar x) = checkRelEqVar f x g es
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
checkRelTy _ _ Eq t1 t2            = void $ unifys [t1] [t2]
checkRelTy _ _ Ne t1 t2            = void $ unifys [t1] [t2]

checkRelTy _ _ Ueq _ _             = return ()
checkRelTy _ _ Une _ _             = return ()
checkRelTy _ e _  t1 t2            = unless (t1 == t2)                 (throwError $ errRel e t1 t2)


-- | Special case for polymorphic singleton variable equality e.g. (x = Set_emp)

checkRelEqVar f x g es             = do tx <- checkSym f x
                                        _  <- checkApp f (Just tx) g es
                                        return ()


-------------------------------------------------------------------------
-- | Sort Unification
-------------------------------------------------------------------------
unify :: Sort -> Sort -> Maybe TVSubst
-------------------------------------------------------------------------
unify t1 t2 = case runCM0 $ unify1 emptySubst t1 t2 of
                Left _   -> Nothing
                Right su -> Just su


-------------------------------------------------------------------------
-- | Fast Unification; `unifyFast True` is just equality
-------------------------------------------------------------------------
unifyFast :: Bool -> Sort -> Sort -> Maybe TVSubst
-------------------------------------------------------------------------
unifyFast False  = unify
unifyFast True   = uMono
  where
    uMono t1 t2
     | t1 == t2  = Just emptySubst
     | otherwise = Nothing

-------------------------------------------------------------------------
unifys :: [Sort] -> [Sort] -> CheckM TVSubst
-------------------------------------------------------------------------
unifys = unifyMany emptySubst

unifyMany :: TVSubst -> [Sort] -> [Sort] -> CheckM TVSubst
unifyMany θ ts ts'
  | length ts == length ts' = foldM (uncurry . unify1) θ $ zip ts ts'
  | otherwise               = throwError $ errUnifyMany ts ts'

unify1 :: TVSubst -> Sort -> Sort -> CheckM TVSubst
unify1 θ (FVar i) t         = unifyVar θ i t
unify1 θ t (FVar i)         = unifyVar θ i t
unify1 θ (FApp t1 t2) (FApp t1' t2')
                            = unifyMany θ [t1, t2] [t1', t2']
unify1 θ (FTC l1) (FTC l2)
  | isListTC l1 && isListTC l2          = return θ
unify1 θ t1@(FAbs _ _) t2               = do t1'<- generalize t1
                                             unifyMany θ [t1'] [t2]
unify1 θ t1 t2@(FAbs _ _)               = do t2' <- generalize t2
                                             unifyMany θ [t1] [t2']
unify1 θ t1 t2
  | t1 == t2                = return θ
  | otherwise               = throwError $ errUnify t1 t2
-- unify1 _ FNum _          = Nothing


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

generalize (FAbs i t)
  = do v      <- refresh 0
       let sub = (i, FVar v)
       subst sub <$> generalize t 
generalize t
  = return t

unifyVar :: TVSubst -> Int -> Sort -> CheckM TVSubst
unifyVar θ i t@(FVar j)
  = case lookupVar i θ of
      Just t'       -> if t == t' then return θ else return $ updateVar j t' θ
      Nothing       -> return $ updateVar i t θ

unifyVar θ i t
  = case lookupVar i θ of
      Just (FVar j) -> return $ updateVar i t $ updateVar j t θ
      Just t'       -> if t == t' then return θ else unify1 θ t t'
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

sortFunction :: Sort -> CheckM (Int, [Sort], Sort)
sortFunction t 
  = case functionSort t of 
     Nothing          -> throwError $ errNonFunction t
     Just (vs, ts, t) -> return (length vs, ts, t)

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
errArgArity g its es e = printf "Measure %s expects %d args but gets %d in %s"
                           (showpp g) (length its) (length es) (showpp e)
errIte e1 e2 t1 t2   = printf "Mismatched branches in Ite: then %s : %s, else %s : %s"
                         (showpp e1) (showpp t1) (showpp e2) (showpp t2)
errCast e t' t       = printf "Cannot cast %s of sort %s to incompatible sort %s"
                         (showpp e) (showpp t') (showpp t)
errUnboundAlts x xs  = printf "Unbound Symbol %s\n Perhaps you meant: %s"
                        (showpp x)
                        (foldr1 (\w s -> w ++ ", " ++ s) (showpp <$> xs))
errNonFunction t     = printf "Sort %s is not a function" (showpp t)
errNonNumeric  l     = printf "FObj sort %s is not numeric" (showpp l)
errNonNumerics l l'  = printf "FObj sort %s and %s are different and not numeric" (showpp l) (showpp l')
errNonFractional  l  = printf "FObj sort %s is not fractional" (showpp l)
errBoolSort     e s  = printf "Expressions %s should have bool sort, but has %s" (showpp e) (showpp s)