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
import           Language.Haskell.Liquid.GHC.TypeRep ()
import           Data.Maybe     (fromMaybe, isJust, mapMaybe)
import           Control.Monad.State hiding (lift)
import           Language.Fixpoint.Misc       ({- mapFst, -}  mapSnd)
import           Language.Haskell.Liquid.Misc (Nat)
import           Language.Haskell.Liquid.GHC.Play (sub, substExpr)
import           Language.Haskell.Liquid.GHC.Misc (unTickExpr, isTupleId, mkAlive)
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
       . tidyTuples
       . rewriteBindWith inlineLoopBreakerTx
       . inlineLoopBreaker
       . rewriteBindWith simplifyPatTuple)
  | otherwise
  = id

simplifyCore :: Config -> Bool
simplifyCore = not . noSimplifyCore

undollar :: RewriteRule
undollar e
    | Just (f, a) <- splitDollarApp e =
      Just $ App f a
    | otherwise = Nothing

tidyTuples :: CoreBind -> CoreBind
tidyTuples ce = case ce of
   NonRec x e -> NonRec x (evalState (go e) [])
   Rec xs -> Rec $ map (fmap (\e -> evalState (go e) [])) xs
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
    go                   = step . txTop
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

-- | Transforms
--
-- > let ds = case e0 of
-- >            pat -> (x1,...,xn)
-- >     y1 = proj1 ds
-- >     ...
-- >     yn = projn ds
-- >  in e1
--
--  to
--
-- > case e0 of
-- >   pat -> e1[y1 := x1,..., yn := xn]
--
-- Note that the transformation changes the meaning of the expression if
-- evaluation order matters. But it changes it in a way that LH cannot
-- distinguish.
--
-- Also transforms a variant of the above
--
-- > let y1 = case v of
-- >            C x1 ... xn -> xi
-- >     y2 = proj2 v
-- >     ...
-- >     yn = projn v
-- >  in e1
--
--  to
--
-- > case v of
-- >   C x1 ... xn -> e1[y1 := x1,..., yn := xn]
--
-- The purpose of the transformations is to unpack all of the variables in
-- @pat@ at once in a single scope when verifying @e1@, which allows LH to
-- see the dependencies between the fields of @pat@.
--
simplifyPatTuple :: RewriteRule
simplifyPatTuple (Let (NonRec x e@(Case _ _ _ [Alt (DataAlt _) _ _])) rest)
  | Just (bs, bs') <- onlyHasATupleInNestedCases e
  , null (bs' L.\\ bs) -- All variables are from the pattern and occur only once
  , let n = length bs'
  , n > 1
  =
    let (nrbinds, e') = takeBinds n rest
        fields = [ (isProjectionOf x ce, b) | b@(_, ce) <- nrbinds ]
        (projs, otherBinds) = L.partition (isJust . fst) fields
        ss = [ (bs' !! i, v) | (Just i, (v, _)) <- projs ]
        e'' = foldr (\(_, (v, ce)) -> Let (NonRec v ce)) e' otherBinds
     in Just $ Let (NonRec x e) $
        replaceAltInNestedCases (Ghc.exprType e') ss e'' e

simplifyPatTuple (Let (NonRec x e@(Case e0 _ _ [Alt (DataAlt _) bs _])) rest)
  | Just v0 <- isVar e0
  , Just i0 <- isProjectionOf v0 e
  , let n = length bs
  , n > 1
  =
    let (nrbinds, e') = takeBinds (n - 1) rest
        fields = [ (isProjectionOf v0 ce, b) | b@(_, ce) <- nrbinds ]
        (projs, otherBinds) = L.partition (isJust . fst) fields
        ss = [ (bs !! i, v) | (Just i, (v, _)) <- (Just i0, (x, e)) : projs ]
        e'' = foldr (\(_, (v, ce)) -> Let (NonRec v ce)) e' otherBinds
     in Just $ replaceAltInNestedCases (Ghc.exprType e') ss e'' e

simplifyPatTuple _
  = Nothing

-- | Replaces an expression at the end of a sequence of nested cases with a
-- single alternative.
replaceAltInNestedCases
  :: Type
  -> [(Var, Var)]
  -> CoreExpr -- ^ The expression to place at the end of the nested cases
  -> CoreExpr -- ^ The expression with the nested cases
  -> CoreExpr
replaceAltInNestedCases t ss ef = go
  where
    go (Case e0 v _ [Alt c bs e1]) =
      let bs' = [ fromMaybe b (lookup b ss) | b <- bs ]
       in Case e0 v t [Alt c bs' (go e1)]
    go _ = ef


-- | Takes at most n binds from an expression that starts with n non-recursive
-- lets.
takeBinds  :: Nat -> CoreExpr -> ([(Var, CoreExpr)], CoreExpr)
takeBinds nat ce = go nat ce
    where
      go 0 e = ([], e)
      go n (Let (NonRec x e) e') =
        let (xes, e'') = go (n-1) e'
         in ((x,e) : xes, e'')
      go _ e = ([], e)

-- | Checks that the binding is a projections of some data constructor.
-- | Yields the index of the field being projected
isProjectionOf :: Var -> CoreExpr -> Maybe Int
isProjectionOf v (Case xe _ _ [Alt (DataAlt _) ys (Var y)])
  | Just xv <- isVar xe
  , v == xv = y `L.elemIndex` ys
isProjectionOf _ _ = Nothing

--------------------------------------------------------------------------------
-- | `substTuple xs ys e'` returns e' [y1 := x1,...,yn := xn]
--------------------------------------------------------------------------------
substTuple :: [Var] -> [Var] -> CoreExpr -> CoreExpr
substTuple xs ys = substExpr (M.fromList $ zip ys xs)

-- | Yields the tuple of variables at the end of nested cases with
-- a single alternative each.
--
-- > case e0 of
-- >   pat0 -> case e1 of
-- >     pat1 -> (x1,...,xn)
--
-- Yields both the bound variables of the patterns, and the
-- variables @x1,...,xn@
onlyHasATupleInNestedCases :: CoreExpr -> Maybe ([Var], [Var])
onlyHasATupleInNestedCases = go []
  where
    go bss (Case _ _ _ [Alt (DataAlt _) bs e]) = go (bs:bss) e
    go bss e = (concat bss,) <$> isTuple e

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
isVar (Tick _ e) = isVar e
isVar _       = Nothing

secondHalf :: [a] -> [a]
secondHalf xs = drop (n `div` 2) xs
  where
    n         = length xs


inlineLoopBreakerTx :: RewriteRule
inlineLoopBreakerTx (Let b e) = Just $ Let (inlineLoopBreaker b) e
inlineLoopBreakerTx _ = Nothing

-- | Changes top level bindings of the form
--
-- > v = \x1...xn ->
-- >   letrec v0 = \y0...ym -> e0
-- >       in v0 xj..xn
--
-- to
--
-- > v = \x1...xj y0...ym ->
-- >   e0 [ v0 := v x1...xj y0...ym ]
--
inlineLoopBreaker :: Bind Id -> Bind Id
inlineLoopBreaker (NonRec x e)
    | Just (lbx, lbe, lbargs) <- hasLoopBreaker be =
       let asPrefix = take (length as - length lbargs) as
           lbe' = sub (M.singleton lbx (ecall asPrefix)) lbe
           mkLams ex = foldr Lam ex (αs ++ asPrefix)
           mkLets ex = foldr Let ex nrbinds
        in Rec [(x, mkLams (mkLets lbe'))]
  where
    (αs, as, e') = collectTyAndValBinders e
    (nrbinds, be) = collectNonRecLets e'

    ecall xs = L.foldl' App (L.foldl' App (Var x) (Type . TyVarTy <$> αs)) (Var <$> xs)

    hasLoopBreaker :: CoreExpr -> Maybe (Var, CoreExpr, [CoreExpr])
    hasLoopBreaker (Let (Rec [(x1, e1)]) e2)
      | (Var x2, args) <- collectArgs e2
      , isLoopBreaker x1
      , x1 == x2
      , all isVar args
      , L.isSuffixOf (mapMaybe getVar args) as
      = Just (x1, e1, args)
    hasLoopBreaker _ = Nothing

    isLoopBreaker =  isStrongLoopBreaker . occInfo . idInfo

    getVar (Var x) = Just x
    getVar _ = Nothing

    isVar (Var _) = True
    isVar _ = False

inlineLoopBreaker bs
  = bs

collectNonRecLets :: Expr t -> ([Bind t], Expr t)
collectNonRecLets = go []
  where go bs (Let b@(NonRec _ _) e') = go (b:bs) e'
        go bs e'                      = (reverse bs, e')
