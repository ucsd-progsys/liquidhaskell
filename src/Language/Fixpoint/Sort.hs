
-- | This module has the functions that perform sort-checking, and related
-- operations on Fixpoint expressions and predicates.

module Language.Fixpoint.Sort  ( 
  -- * Checking Well-Formedness
    checkSorted
  , checkSortedReft
  , checkSortedReftFull
  , pruneUnsortedReft
  ) where



import Language.Fixpoint.Types
import Language.Fixpoint.Misc
import Text.PrettyPrint.HughesPJ
import Text.Printf
import Control.Monad.Error (catchError, throwError)
import Control.Monad
import Control.Applicative
import Data.Maybe           (fromMaybe, catMaybes)
import qualified Data.HashMap.Strict as M

import Debug.Trace          (trace)

-- | Types used throughout checker

type CheckM a = Either String a
type Env      = Symbol -> SESearch Sort
fProp         = FApp boolFTyCon [] 
-- fProp         = FApp propFTyCon [] 

-------------------------------------------------------------------------
-- | Checking Refinements -----------------------------------------------
-------------------------------------------------------------------------

checkSortedReft :: SEnv SortedReft -> [Symbol] -> SortedReft -> Maybe Doc
checkSortedReft env xs sr = applyNonNull Nothing error unknowns 
  where 
    error                 = Just . (text "Unknown symbols:" <+>) . toFix 
    unknowns              = [ x | x <- syms sr, not (x `elem` v : xs), not (x `memberSEnv` env)]    
    Reft (v,_)            = sr_reft sr 

checkSortedReftFull :: Checkable a => SEnv SortedReft -> a -> Maybe Doc
checkSortedReftFull γ t
  = case check γ' t of
      Left err -> Just (text err)
      Right _  -> Nothing
    where 
      γ' = mapSEnv sr_sort γ  

checkSorted :: Checkable a => SEnv Sort -> a -> Maybe Doc
checkSorted γ t
  = case check γ t of
      Left err -> Just (text err)
      Right _  -> Nothing

pruneUnsortedReft :: SEnv Sort -> SortedReft -> SortedReft
pruneUnsortedReft γ (RR s (Reft (v, ras)))
  = RR s (Reft (v, catMaybes (go <$> ras))) 
  where 
    go r = case checkRefa f r of
            Left war -> trace (wmsg war r) $ Nothing
            Right _  -> Just r
    γ' = insertSEnv v s γ
    f  = (`lookupSEnvWithDistance` γ')

    wmsg t r = "WARNING: prune unsorted reft:\n" ++ showFix r ++ "\n" ++ t

checkRefa f (RConc p) = checkPred f p
checkRefa f _         = return ()


class Checkable a where
  check :: SEnv Sort -> a -> CheckM ()

instance Checkable Refa where
  check γ = checkRefa (`lookupSEnvWithDistance` γ)

instance Checkable Expr where
  check γ e = do {checkExpr f e; return ()}
   where f =  (`lookupSEnvWithDistance` γ)

instance Checkable Pred where
  check γ = checkPred f
   where f = (`lookupSEnvWithDistance` γ)

instance Checkable SortedReft where
  check γ (RR s (Reft (v, ras))) = mapM_ (check γ') ras
   where γ' = insertSEnv v s γ  

-------------------------------------------------------------------------
-- | Checking Expressions -----------------------------------------------
-------------------------------------------------------------------------

checkExpr                  :: Env -> Expr -> CheckM Sort 

checkExpr _ EBot           = throwError "Type Error: Bot"
checkExpr _ (ECon _)       = return FInt 
checkExpr f (EVar x)       = checkSym f x
checkExpr f (EBin o e1 e2) = checkOp f e1 o e2
checkExpr f (EIte p e1 e2) = checkIte f p e1 e2
checkExpr f (ECst e t)     = checkCst f t e
checkExpr f (EApp g es)    = checkApp f Nothing g es
checkExpr f (ELit _ t)     = return t

-- | Helper for checking symbol occurrences

checkSym f x               
  = case f x of 
     Found s -> return s
     Alts xs -> throwError $ errUnboundAlts x xs
--   $ traceFix ("checkSym: x = " ++ showFix x) (f x)

-- | Helper for checking if-then-else expressions

checkIte f p e1 e2 
  = do tp <- checkPred f p
       t1 <- checkExpr f e1
       t2 <- checkExpr f e2
       if t1 == t2 
         then return t1
         else throwError (errIte e1 e2 t1 t2) 

-- | Helper for checking cast expressions 

checkCst f t (EApp g es) 
  = checkApp f (Just t) g es
checkCst f t e           
  = do t' <- checkExpr f e
       if t == t' 
         then return t
         else throwError (errCast e t' t)

-- | Helper for checking uninterpreted function applications

checkApp' f to g es 
  = do gt           <- checkSym f g
       (n, its, ot) <- sortFunction gt
       unless (length its == length es) $ throwError (errArgArity g its es)
       ets          <- mapM (checkExpr f) es
       θ            <- unify its ets
       let t         = apply θ ot
       case to of
         Nothing    -> return (θ, t)
         Just t'    -> do θ' <- unifyMany θ [t] [t']
                          return (θ', apply θ' t)


checkApp f to g es
  = snd <$> checkApp' f to g es


-- | Helper for checking binary (numeric) operations

checkOp f e1 o e2 
  = do t1 <- checkExpr f e1
       t2 <- checkExpr f e2
       checkOpTy f (EBin o e1 e2) t1 t2

checkOpTy f _ FInt FInt          
  = return FInt

checkOpTy f e t@(FObj l) t'@(FObj l')
  | l == l'
  = checkNumeric f l >> return t

checkOpTy f e t t'
  = throwError $ errOp e t t'

checkNumeric f l
  = do t <- checkSym f l
       unless (t == FNum) (throwError $ errNonNumeric l)
       return ()

-------------------------------------------------------------------------
-- | Checking Predicates ------------------------------------------------
-------------------------------------------------------------------------

checkPred                  :: Env -> Pred -> CheckM () 

checkPred f PTrue          = return ()
checkPred f PFalse         = return ()
checkPred f (PBexp e)      = checkPredBExp f e 
checkPred f (PNot p)       = checkPred f p
checkPred f (PImp p p')    = mapM_ (checkPred f) [p, p'] 
checkPred f (PIff p p')    = mapM_ (checkPred f) [p, p']
checkPred f (PAnd ps)      = mapM_ (checkPred f) ps
checkPred f (POr ps)       = mapM_ (checkPred f) ps
checkPred f (PAtom r e e') = checkRel f r e e'
checkPred f p              = throwError $ errUnexpectedPred p

checkPredBExp f e          = do t <- checkExpr f e
                                unless (t == fProp) (throwError $ errBExp e t)
                                return ()
  

-- | Checking Relations

checkRel f Eq (EVar x) (EApp g es) = checkRelEqVar f x g es
checkRel f Eq (EApp g es) (EVar x) = checkRelEqVar f x g es
checkRel f r  e1 e2                = do t1 <- checkExpr f e1
                                        t2 <- checkExpr f e2
                                        checkRelTy f (PAtom r e1 e2) r t1 t2

checkRelTy :: (Fixpoint a) => Env -> a -> Brel -> Sort -> Sort -> CheckM ()
checkRelTy f _ _ (FObj l) (FObj l') | l /= l' 
  = (checkNumeric f l >> checkNumeric f l') `catchError` (\_ -> throwError $ errNonNumerics l l') 
checkRelTy f _ _ FInt (FObj l)     = (checkNumeric f l) `catchError` (\_ -> throwError $ errNonNumeric l) 
checkRelTy f _ _ (FObj l) FInt     = (checkNumeric f l) `catchError` (\_ -> throwError $ errNonNumeric l)
checkRelTy _ e Eq t1 t2            = unless (t1 == t2 && t1 /= fProp)  (throwError $ errRel e t1 t2)
checkRelTy _ e Ne t1 t2            = unless (t1 == t2 && t1 /= fProp)  (throwError $ errRel e t1 t2)
checkRelTy _ e Ueq t1 t2           = unless (isAppTy t1 && isAppTy t2) (throwError $ errRel e t1 t2)
checkRelTy _ e Une t1 t2           = unless (isAppTy t1 && isAppTy t2) (throwError $ errRel e t1 t2)
checkRelTy _ e _  t1 t2            = unless (t1 == t2)                 (throwError $ errRel e t1 t2)


-- | Special case for polymorphic singleton variable equality e.g. (x = Set_emp) 

checkRelEqVar f x g es             = do tx <- checkSym f x
                                        _  <- checkApp f (Just tx) g es
                                        return ()

-- | Special case for Unsorted Dis/Equality
isAppTy :: Sort -> Bool
isAppTy (FApp _ _) = True
isAppTy _          = False

-------------------------------------------------------------------------
-- | Error messages -----------------------------------------------------
-------------------------------------------------------------------------

errUnify t1 t2       = printf "Cannot unify %s with %s" (showFix t1) (showFix t2)

errUnifyMany ts ts'  = printf "Cannot unify types with different cardinalities %s and %s" 
                         (showFix ts) (showFix ts')

errRel e t1 t2       = printf "Invalid Relation %s with operand types %s and %s" 
                         (showFix e) (showFix t1) (showFix t2)

errBExp e t          = printf "BExp %s with non-propositional type %s" (showFix e) (showFix t)

errOp e t t' 
  | t == t'          = printf "Operands have non-numeric types %s in %s"  
                         (showFix t) (showFix e)
  | otherwise        = printf "Operands have different types %s and %s in %s" 
                         (showFix t) (showFix t') (showFix e)

errArgArity g its es = printf "Measure %s expects %d args but gets %d in %s" 
                         (showFix g) (length its) (length es) (showFix (EApp g es))

errIte e1 e2 t1 t2   = printf "Mismatched branches in Ite: then %s : %s, else %s : %s" 
                         (showFix e1) (showFix t1) (showFix e2) (showFix t2) 

errCast e t' t       = printf "Cannot cast %s of sort %s to incompatible sort %s" 
                         (showFix e) (showFix t') (showFix t)

errUnbound x         = printf "Unbound Symbol %s" (showFix x)
errUnboundAlts x xs  = printf "Unbound Symbol %s\n Perhaps you meant: %s" 
                        (showFix x) 
                        (foldr1 (\w s -> w ++ ", " ++ s) (showFix <$> xs))

errNonFunction t     = printf "Sort %s is not a function" (showFix t)

errNonNumeric  l     = printf "FObj sort %s is not numeric" (showFix l)
errNonNumerics l l'   = printf "FObj sort %s and %s are different and not numeric" (showFix l) (showFix l')

errUnexpectedPred p  = printf "Sort Checking: Unexpected Predicate %s" (showFix p)

-------------------------------------------------------------------------
-- | Utilities for working with sorts -----------------------------------
-------------------------------------------------------------------------

-- | Unification of Sorts

unify                              = unifyMany (Th M.empty)

unifyMany θ ts ts' 
  | length ts == length ts'        = foldM (uncurry . unify1) θ $ zip ts ts'
  | otherwise                      = throwError $ errUnifyMany ts ts'

-- unify1 _ FNum _                    = Nothing
unify1 θ (FVar i) t                = unifyVar θ i t
unify1 θ t (FVar i)                = unifyVar θ i t
unify1 θ (FApp c ts) (FApp c' ts')  
  | c == c'                        = unifyMany θ ts ts' 
unify1 θ t1 t2  
  | t1 == t2                       = return θ
  | otherwise                      = throwError $ errUnify t1 t2

unifyVar θ i t 
  = case lookupVar i θ of
      Just t' -> if t == t' then return θ else throwError (errUnify t t') 
      Nothing -> return $ updateVar i t θ 

-- | Sort Substitutions
newtype TVSubst      = Th (M.HashMap Int Sort) 

-- | API for manipulating substitutions
lookupVar i (Th m)   = M.lookup i m
updateVar i t (Th m) = Th (M.insert i t m)

-------------------------------------------------------------------------
-- | Applying a Type Substitution ---------------------------------------
-------------------------------------------------------------------------

apply θ          = sortMap f
  where
    f t@(FVar i) = fromMaybe t (lookupVar i θ)
    f t          = t

sortMap f (FFunc n ts) = FFunc n (sortMap f <$> ts)
sortMap f (FApp  c ts) = FApp  c (sortMap f <$> ts)
sortMap f t            = f t

------------------------------------------------------------------------
-- | Deconstruct a function-sort ---------------------------------------
------------------------------------------------------------------------

sortFunction (FFunc n ts') = return (n, ts, t) 
  where 
    ts                     = take numArgs ts'
    t                      = last ts'
    numArgs                = length ts' - 1

sortFunction t             = throwError $ errNonFunction t 
