{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE FlexibleContexts          #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

-- | This module contains functions for recursively "rewriting"
--   GHC core using "rules".

module Language.Haskell.Liquid.Transforms.Rewrite
  ( -- * Top level rewrite function
    rewriteBinds

  -- * Low-level Rewriting Function
  -- , rewriteWith

  -- * Rewrite Rule
  -- ,  RewriteRule

  ) where

import           Liquid.GHC.API as Ghc hiding (showPpr, substExpr)
import           Liquid.GHC.TypeRep ()
import           Data.Maybe     (fromMaybe)
import           Control.Monad.State hiding (lift)
import           Language.Fixpoint.Misc       ({- mapFst, -}  mapSnd)
import qualified          Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Misc (safeZipWithError, Nat)
import           Liquid.GHC.Play (substExpr)
import           Liquid.GHC.Resugar
import           Liquid.GHC.Misc (unTickExpr, isTupleId, showPpr, mkAlive) -- , showPpr, tracePpr)
import           Language.Haskell.Liquid.UX.Config  (Config, noSimplifyCore)
import qualified Data.List as L
import qualified Data.HashMap.Strict as M

--------------------------------------------------------------------------------
-- | Top-level rewriter --------------------------------------------------------
--------------------------------------------------------------------------------
rewriteBinds :: Config -> [CoreBind] -> [CoreBind]
rewriteBinds cfg
  | simplifyCore cfg
  = fmap (normalizeTuples 
       . rewriteBindWith undollar 
       . rewriteBindWith tidyTuples 
       . rewriteBindWith simplifyPatTuple)
  | otherwise
  = id

simplifyCore :: Config -> Bool
simplifyCore = not . noSimplifyCore

undollar :: RewriteRule
undollar = go 
  where 
    go e 
     -- matches `$ t1 t2 t3 f a`  
     | App e1 a  <- untick e
     , App e2 f  <- untick e1
     , App e3 t3 <- untick e2 
     , App e4 t2 <- untick e3 
     , App d t1  <- untick e4 
     , Var v     <- untick d 
     , v `hasKey` dollarIdKey
     , Type _    <- untick t1
     , Type _    <- untick t2
     , Type _    <- untick t3
     = Just $ App f a 
    go (Tick t e)
      = Tick t <$> go e
    go (Let (NonRec x ex) e)
      = do ex' <- go ex
           e'  <- go e
           return $ Let (NonRec x ex') e'
    go (Let (Rec bes) e)
      = Let <$> (Rec <$> mapM goRec bes) <*> go e
    go (Case e x t alts)
      = Case e x t <$> mapM goAlt alts
    go (App e1 e2)
      = App <$> go e1 <*> go e2
    go (Lam x e)
      = Lam x <$> go e
    go (Cast e c)
      = (`Cast` c) <$> go e
    go e
      = return e

    goRec (x, e)
      = (x,) <$> go e

    goAlt (Alt c bs e)
      = Alt c bs <$> go e

  
 

untick :: CoreExpr -> CoreExpr 
untick (Tick _ e) = untick e 
untick e          = e 

tidyTuples :: RewriteRule
tidyTuples ce = Just $ evalState (go ce) []
  where
    go (Tick t e)
      = Tick t <$> go e
    go (Let (NonRec x ex) e)
      = do ex' <- go ex
           e'  <- go e
           return $ Let (NonRec x ex') e'
    go (Let (Rec bes) e)
      = Let <$> (Rec <$> mapM goRec bes) <*> go e
    go (Case (Var v) x t alts)
      = Case (Var v) x t <$> mapM (goAltR v) alts
    go (Case e x t alts)
      = Case e x t <$> mapM goAlt alts
    go (App e1 e2)
      = App <$> go e1 <*> go e2
    go (Lam x e)
      = Lam x <$> go e
    go (Cast e c)
      = (`Cast` c) <$> go e
    go e
      = return e

    goRec (x, e)
      = (x,) <$> go e

    goAlt (Alt c bs e)
      = Alt c bs <$> go e

    goAltR v (Alt c bs e)
      = do m <- get
           case L.lookup (c,v) m of
            Just bs' -> return (Alt c bs' (substTuple bs' bs e))
            Nothing  -> do let bs' = mkAlive <$> bs
                           modify (((c,v),bs'):)
                           return (Alt c bs' e)



normalizeTuples :: CoreBind -> CoreBind
normalizeTuples cb
  | NonRec x e <- cb
  = NonRec x $ go e
  | Rec xes <- cb
  = let (xs,es) = unzip xes in
    Rec $ zip xs (go <$> es)
  where
    go (Let (NonRec x ex) e)
      | Case _ _ _ alts  <- unTickExpr ex
      , [Alt _ vs (Var z)] <- alts
      , z `elem` vs
      = Let (NonRec z (go ex)) (substTuple [z] [x] (go e))
    go (Let (NonRec x ex) e)
      = Let (NonRec x (go ex)) (go e)
    go (Let (Rec xes) e)
      = Let (Rec (mapSnd go <$> xes)) (go e)
    go (App e1 e2)
      = App (go e1) (go e2)
    go (Lam x e)
      = Lam x (go e)
    go (Case e b t alt)
      = Case (go e) b t ((\(Alt c bs e') -> Alt c bs (go e')) <$> alt)
    go (Cast e c)
      = Cast (go e) c
    go (Tick t e)
      = Tick t (go e)
    go (Type t)
      = Type t
    go (Coercion c)
      = Coercion c
    go (Lit l)
      = Lit l
    go (Var x)
      = Var x


--------------------------------------------------------------------------------
-- | A @RewriteRule@ is a function that maps a CoreExpr to another
--------------------------------------------------------------------------------
type RewriteRule = CoreExpr -> Maybe CoreExpr
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
rewriteBindWith :: RewriteRule -> CoreBind -> CoreBind
--------------------------------------------------------------------------------
rewriteBindWith r (NonRec x e) = NonRec x (rewriteWith r e)
rewriteBindWith r (Rec xes)    = Rec    (mapSnd (rewriteWith r) <$> xes)

--------------------------------------------------------------------------------
rewriteWith :: RewriteRule -> CoreExpr -> CoreExpr
--------------------------------------------------------------------------------
rewriteWith tx           = go
  where
    go                   = txTop . step
    txTop e              = fromMaybe e (tx e)
    goB (Rec xes)        = Rec         (mapSnd go <$> xes)
    goB (NonRec x e)     = NonRec x    (go e)
    step (Let b e)       = Let (goB b) (go e)
    step (App e e')      = App (go e)  (go e')
    step (Lam x e)       = Lam x       (go e)
    step (Cast e c)      = Cast (go e) c
    step (Tick t e)      = Tick t      (go e)
    step (Case e x t cs) = Case (go e) x t ((\(Alt c bs e') -> Alt c bs (go e')) <$> cs)
    step e@(Type _)      = e
    step e@(Lit _)       = e
    step e@(Var _)       = e
    step e@(Coercion _)  = e


--------------------------------------------------------------------------------
-- | Rewriting Pattern-Match-Tuples --------------------------------------------
--------------------------------------------------------------------------------

{-
    let CrazyPat x1 ... xn = e in e'

    let t : (t1,...,tn) = "CrazyPat e ... (y1, ..., yn)"
        xn = Proj t n
        ...
        x1 = Proj t 1
    in
        e'

    "crazy-pat"
 -}

{- [NOTE] The following is the structure of a @PatMatchTup@

      let x :: (t1,...,tn) = E[(x1,...,xn)]
          yn = case x of (..., yn) -> yn
          …
          y1 = case x of (y1, ...) -> y1
      in
          E'

  GOAL: simplify the above to:

      E [ (x1,...,xn) := E' [y1 := x1,...,yn := xn] ]

  TODO: several tests (e.g. tests/pos/zipper000.hs) fail because
  the above changes the "type" the expression `E` and in "other branches"
  the new type may be different than the old, e.g.

     let (x::y::_) = e in
     x + y

     let t = case e of
               h1::t1 -> case t1 of
                            (h2::t2) ->  (h1, h2)
                            DEFAULT  ->  error @ (Int, Int)
               DEFAULT   -> error @ (Int, Int)
         x = case t of (h1, _) -> h1
         y = case t of (_, h2) -> h2
     in
         x + y

  is rewritten to:

              h1::t1    -> case t1 of
                            (h2::t2) ->  h1 + h2
                            DEFAULT  ->  error @ (Int, Int)
              DEFAULT   -> error @ (Int, Int)

     case e of
       h1 :: h2 :: _ -> h1 + h2
       DEFAULT       -> error @ (Int, Int)

  which, alas, is ill formed.

-}

--------------------------------------------------------------------------------

-- simplifyPatTuple :: RewriteRule
-- simplifyPatTuple e =
--  case simplifyPatTuple' e of
--    Just e' -> if Ghc.exprType e == Ghc.exprType e'
--                 then Just e'
--                 else Just (tracePpr ("YIKES: RWR " ++ showPpr e) e')
--    Nothing -> Nothing


_safeSimplifyPatTuple :: RewriteRule
_safeSimplifyPatTuple e
  | Just e' <- simplifyPatTuple e
  , Ghc.exprType e' == Ghc.exprType e
  = Just e'
  | otherwise
  = Nothing

--------------------------------------------------------------------------------
simplifyPatTuple :: RewriteRule
--------------------------------------------------------------------------------

_tidyAlt :: Int -> Maybe CoreExpr -> Maybe CoreExpr

_tidyAlt n (Just (Let (NonRec cb expr) rest))
  | Just (yes, e') <- takeBinds n rest
  = Just $ Let (NonRec cb expr) $ foldl (\e (x, ex) -> Let (NonRec x ex) e) e' (reverse $ go $ reverse yes)

  where
    go xes@((_, e):_) = let bs = grapBinds e in mapSnd (replaceBinds bs) <$> xes
    go [] = []
    replaceBinds bs (Case c x t alt) = Case c x t (replaceBindsAlt bs <$> alt)
    replaceBinds bs (Tick t e)       = Tick t (replaceBinds bs e)
    replaceBinds _ e                 = e
    replaceBindsAlt bs (Alt c _ e)     = Alt c bs e

    grapBinds (Case _ _ _ alt) = grapBinds' alt
    grapBinds (Tick _ e) = grapBinds e
    grapBinds _ = []
    grapBinds' [] = []
    grapBinds' (Alt _ bs _ : _) = bs

_tidyAlt _ e
  = e

simplifyPatTuple (Let (NonRec x e) rest)
  | Just (n, ts  ) <- varTuple x
  , 2 <= n
  , Just (yes, e') <- takeBinds n rest
  , let ys          = fst <$> yes
  , Just _         <- hasTuple ys e
  , matchTypes yes ts
  = replaceTuple ys e e'

simplifyPatTuple _
  = Nothing

varTuple :: Var -> Maybe (Int, [Type])
varTuple x
  | TyConApp c ts <- Ghc.varType x
  , isTupleTyCon c
  = Just (length ts, ts)
  | otherwise
  = Nothing

takeBinds  :: Nat -> CoreExpr -> Maybe ([(Var, CoreExpr)], CoreExpr)
takeBinds nat ce
  | nat < 2     = Nothing
  | otherwise = {- mapFst reverse <$> -} go nat ce
    where
      go 0 e                      = Just ([], e)
      go n (Let (NonRec x e) e')  = do (xes, e'') <- go (n-1) e'
                                       Just ((x,e) : xes, e'')
      go _ _                      = Nothing

matchTypes :: [(Var, CoreExpr)] -> [Type] -> Bool
matchTypes xes ts =  xN == tN
                  && all (uncurry eqType) (safeZipWithError msg xts ts)
                  && all isProjection es
  where
    xN            = length xes
    tN            = length ts
    xts           = Ghc.varType <$> xs
    (xs, es)      = unzip xes
    msg           = "RW:matchTypes"

isProjection :: CoreExpr -> Bool
isProjection e = case lift e of
                   Just PatProject{} -> True
                   _                 -> False

--------------------------------------------------------------------------------
-- | `hasTuple ys e` CHECKS if `e` contains a tuple that "looks like" (y1...yn)
--------------------------------------------------------------------------------
hasTuple :: [Var] -> CoreExpr -> Maybe [Var]
--------------------------------------------------------------------------------
hasTuple ys = stepE
  where
    stepE e
     | Just xs <- isVarTup ys e = Just xs
     | otherwise                = go e
    stepA (Alt DEFAULT _ _)     = Nothing
    stepA (Alt _ _ e)           = stepE e
    go (Let _ e)                = stepE e
    go (Case _ _ _ cs)          = msum (stepA <$> cs)
    go _                        = Nothing

--------------------------------------------------------------------------------
-- | `replaceTuple ys e e'` REPLACES tuples that "looks like" (y1...yn) with e'
--------------------------------------------------------------------------------

replaceTuple :: [Var] -> CoreExpr -> CoreExpr -> Maybe CoreExpr
replaceTuple ys ce ce'           = stepE ce
  where
    t'                          = Ghc.exprType ce'
    stepE e
     | Just xs <- isVarTup ys e = Just $ substTuple xs ys ce'
     | otherwise                = go e
    stepA (Alt DEFAULT xs err)  = Just (Alt DEFAULT xs (replaceIrrefutPat t' err))
    stepA (Alt c xs e)          = Alt c xs   <$> stepE e
    go (Let b e)                = Let b      <$> stepE e
    go (Case e x t cs)          = fixCase e x t <$> mapM stepA cs
    go _                        = Nothing

_showExpr :: CoreExpr -> String
_showExpr = show'
  where
    show' (App e1 e2) = show' e1 ++ " " ++ show' e2
    show' (Var x)     = _showVar x
    show' (Let (NonRec x ex) e) = "Let " ++ _showVar x ++ " = " ++ show' ex ++ "\nIN " ++ show' e
    show' (Tick _ e) = show' e
    show' (Case e x _ alt) = "Case " ++ _showVar x ++ " = " ++ show' e ++ " OF " ++ unlines (showAlt' <$> alt)
    show' e           = showPpr e

    showAlt' (Alt c bs e) = showPpr c ++ unwords (_showVar <$> bs) ++ " -> " ++ show' e

_showVar :: Var -> String
_showVar = show . F.symbol

_errorSkip :: String -> a -> b
_errorSkip x _ = error x

-- replaceTuple :: [Var] -> CoreExpr -> CoreExpr -> Maybe CoreExpr
-- replaceTuple ys e e' = tracePpr msg (_replaceTuple ys e e')
--  where
--    msg = "replaceTuple: ys = " ++ showPpr ys ++
--                        " e = " ++ showPpr e  ++
--                        " e' =" ++ showPpr e'

-- | The substitution (`substTuple`) can change the type of the overall
--   case-expression, so we must update the type of each `Case` with its
--   new, possibly updated type. See:
--   https://github.com/ucsd-progsys/liquidhaskell/pull/752#issuecomment-228946210

fixCase :: CoreExpr -> Var -> Type -> ListNE (Alt Var) -> CoreExpr
fixCase e x _t cs' = Case e x t' cs'
  where
    t'            = Ghc.exprType body
    Alt _ _ body  = c
    c:_           = cs'

{-@  type ListNE a = {v:[a] | len v > 0} @-}
type ListNE a = [a]

replaceIrrefutPat :: Type -> CoreExpr -> CoreExpr
replaceIrrefutPat t (App (Lam z e) eVoid)
  | Just e' <- replaceIrrefutPat' t e
  = App (Lam z e') eVoid

replaceIrrefutPat t e
  | Just e' <- replaceIrrefutPat' t e
  = e'

replaceIrrefutPat _ e
  = e

replaceIrrefutPat' :: Type -> CoreExpr -> Maybe CoreExpr
replaceIrrefutPat' t e
  | (Var x, rep:_:args) <- collectArgs e
  , isIrrefutErrorVar x
  = Just (Ghc.mkCoreApps (Var x) (rep : Type t : args))
  | otherwise
  = Nothing

isIrrefutErrorVar :: Var -> Bool
-- isIrrefutErrorVar _x = False -- Ghc.iRREFUT_PAT_ERROR_ID == x -- TODO:GHC-863
isIrrefutErrorVar x = x == Ghc.pAT_ERROR_ID

--------------------------------------------------------------------------------
-- | `substTuple xs ys e'` returns e' [y1 := x1,...,yn := xn]
--------------------------------------------------------------------------------
substTuple :: [Var] -> [Var] -> CoreExpr -> CoreExpr
substTuple xs ys = substExpr (M.fromList $ zip ys xs)

--------------------------------------------------------------------------------
-- | `isVarTup xs e` returns `Just ys` if e == (y1, ... , yn) and xi ~ yi
--------------------------------------------------------------------------------

isVarTup :: [Var] -> CoreExpr -> Maybe [Var]
isVarTup xs e
  | Just ys <- isTuple e
  , eqVars xs ys        = Just ys
isVarTup _ _             = Nothing

eqVars :: [Var] -> [Var] -> Bool
eqVars xs ys = {- F.tracepp ("eqVars: " ++ show xs' ++ show ys') -} xs' == ys'
  where
    xs' = {- F.symbol -} show <$> xs
    ys' = {- F.symbol -} show <$> ys

isTuple :: CoreExpr -> Maybe [Var]
isTuple e
  | (Var t, es) <- collectArgs e
  , isTupleId t
  , Just xs     <- mapM isVar (secondHalf es)
  = Just xs
  | otherwise
  = Nothing

isVar :: CoreExpr -> Maybe Var
isVar (Var x) = Just x
isVar _       = Nothing

secondHalf :: [a] -> [a]
secondHalf xs = drop (n `div` 2) xs
  where
    n         = length xs
