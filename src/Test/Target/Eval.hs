{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
module Test.Target.Eval ( eval, evalWith, evalExpr ) where



import           Control.Monad.Catch
import           Control.Monad.State
import qualified Data.HashMap.Strict             as M

import           Data.List
import           Data.Maybe
import qualified Data.Set                        as S


import           Text.Printf

import qualified GHC

import           Language.Fixpoint.Smt.Types
import           Language.Fixpoint.Types         hiding (R)
import           Language.Haskell.Liquid.Types   hiding (var)

import           Test.Target.Expr
import           Test.Target.Monad

import           Test.Target.Types
import           Test.Target.Util

-- import           Debug.Trace

-- | Evaluate a refinement with the given expression substituted for the value
-- variable.
eval :: Reft -> Expr -> Target Bool
eval r e = do
  cts <- gets freesyms
  evalWith (M.fromList $ map (\(_, c) -> (c, c `VC` [])) cts) r e

-- | Evaluate a refinement with the given expression substituted for the value
-- variable, in the given environment of free symbols.
evalWith :: M.HashMap Symbol Val -> Reft -> Expr -> Target Bool
evalWith m (Reft (v, p)) x
  = do xx <- evalExpr x m
                  -- FIXME: tidy is suspicious!!
       evalPred p (M.insert (tidySymbol v) xx m)


evalPred :: Expr -> M.HashMap Symbol Val -> Target Bool
evalPred PTrue           _ = return True
evalPred PFalse          _ = return False
evalPred (PAnd ps)       m = and <$> sequence [evalPred p m | p <- ps]
evalPred (POr ps)        m = or  <$> sequence [evalPred p m | p <- ps]
evalPred (PNot p)        m = not <$> evalPred p m
evalPred (PImp p q)      m = do pv <- evalPred p m
                                if pv
                                   then evalPred q m
                                   else return True
evalPred (PIff p q)      m = and <$> sequence [ evalPred (p `imp` q) m
                                              , evalPred (q `imp` p) m
                                              ]
evalPred (PAtom b e1 e2) m = evalBrel b <$> evalExpr e1 m <*> evalExpr e2 m
evalPred e@(splitEApp_maybe -> Just (f, es))    m
  = do isThy <- isTheorySymbol f
       if isThy
         then evalPredBlob1 m f es
         else evalPredBlob2 m e f es
-- evalPred (PBexp e)       m = (==0) <$> evalPred e m
evalPred p               _ = throwM $ EvalError $ "evalPred: " ++ show p
-- evalExpr (PAll ss p)     m = undefined
-- evalExpr PTop            m = undefined
-- evalExpr :: Expr -> M.HashMap Symbol Expr -> Target Expr


evalPredBlob1 :: M.HashMap Symbol Val -> Symbol -> [Expr] -> Target Bool
evalPredBlob1 m f es
  = mapM (`evalExpr` m) es >>= \es' -> fromExpr <$> evalSet f es'

evalPredBlob2 :: Show a => M.HashMap Symbol Val -> a -> Symbol -> [Expr] -> Target Bool
evalPredBlob2 m e f es
  = filter ((==f) . val . name) <$> gets measEnv >>= \case
      [] -> error $ "evalPred: cannot evaluate " ++ show e -- VC f <$> mapM (`evalExpr` m) es
                      --FIXME: should really extend this to multi-param measures..
      ms -> do e' <- evalExpr (head es) m
               fromExpr <$> applyMeasure (symbolString f) (concatMap eqns ms) e' m

fromExpr :: Val -> Bool
fromExpr (VB True) = True
fromExpr (VB False) = False
fromExpr e = error $ "fromExpr: " ++ show e ++ " is not boolean"

evalExpr :: Expr -> M.HashMap Symbol Val -> Target Val
evalExpr e m = do
  -- traceShowM ("evalExpr", e)
  evalExpr' e m

evalExpr' :: Expr -> M.HashMap Symbol Val -> Target Val
evalExpr' (ECon i)       _ = return $! VV i
evalExpr' (EVar x)       m = return $! -- traceShow (x,m)
                                       -- FIXME: tidy is fishy!!
                                       -- datacons are embedded as vars and may not
                                       -- be in the freesym environment
                                    fromMaybe (VC x []) (M.lookup (tidySymbol x) m)
evalExpr' (ESym s)       _ = return $! VX s
evalExpr' (EBin b e1 e2) m = evalBop b <$> evalExpr' e1 m <*> evalExpr' e2 m
evalExpr' (splitEApp_maybe -> Just (f, es))    m
  = do isThy <- isTheorySymbol f
       if isThy then evalExprBlob1 m f es
                else evalExprBlob2 m f es

evalExpr' (EIte p e1 e2) m
  = do b <- evalPred p m
       if b
         then evalExpr' e1 m
         else evalExpr' e2 m
evalExpr' e              _ = throwM $ EvalError $ printf "evalExpr(%s)" (show e)

isTheorySymbol :: Symbol -> Target Bool
isTheorySymbol f = do
  theorySymbols <- seTheory . ctxSymEnv <$> gets smtContext
  return (f == "Set_emp" || f == "Set_sng" || f `memberSEnv` theorySymbols)

evalExprBlob1 :: M.HashMap Symbol Val -> Symbol -> [Expr] -> Target Val
evalExprBlob1 m f es
  = mapM (`evalExpr'` m) es >>= \es' -> evalSet f es'

evalExprBlob2 :: M.HashMap Symbol Val -> Symbol -> [Expr] -> Target Val
evalExprBlob2 m f es
  = filter ((==f) . val . name) <$> gets measEnv >>= \case
      [] -> VC f <$> mapM (`evalExpr'` m) es   --FIXME: should really extend this to multi-param measures..
      ms -> do e' <- evalExpr' (head es) m
               applyMeasure (symbolString f) (concatMap eqns ms) e' m

evalBrel :: Brel -> Val -> Val -> Bool
evalBrel Eq = (==)
evalBrel Ne = (/=)
evalBrel Ueq = (==)
evalBrel Une = (/=)
evalBrel Gt = (>)
evalBrel Ge = (>=)
evalBrel Lt = (<)
evalBrel Le = (<=)

applyMeasure :: String -> [Language.Haskell.Liquid.Types.Def SpecType GHC.DataCon] -> Val -> M.HashMap Symbol Val -> Target Val
applyMeasure name eqns (VC f es) env -- (splitEApp_maybe -> Just (f, es)) env
  = do
       -- traceShowM ("applyMeasure", name)
       meq >>= \eq -> evalBody eq es env
  where
    -- FIXME: tidy is fishy!!
    ct = symbolString . tidySymbol $ case f of
      "GHC.Types.[]" -> "[]"
      "GHC.Types.:"  -> ":"
      "GHC.Tuple.(,)" -> "(,)"
      "GHC.Tuple.(,,)" -> "(,,)"
      "GHC.Tuple.(,,,)" -> "(,,,)"
      "GHC.Tuple.(,,,,)" -> "(,,,,)"
      x -> x
    meq = case find ((==ct) . show . ctor) eqns of
           Nothing -> throwM $ EvalError $ printf "applyMeasure(%s): no equation for %s" name (show ct)
           Just x -> return x

applyMeasure n _ e           _
  = throwM $ EvalError $ printf "applyMeasure(%s, %s)" n (showpp e)

-- setSym :: Symbol
-- setSym = "LC_SET"

-- nubSort :: [Expr] -> [Expr]
-- nubSort = nub . Data.List.sort

-- mkSet :: [Expr] -> Expr
-- mkSet = app setSym . nubSort

evalSet :: Symbol -> [Val] -> Target Val
evalSet "Set_emp" [VS s]
  = return $! if S.null s then VB True else VB False
evalSet "Set_sng" [v]
  = return $! VS $ S.singleton v
-- TODO!!
evalSet "Set_add" [v, VS s]
  = return $! VS $ S.insert v s
evalSet "Set_cap" [VS s1, VS s2]
  = return $! VS $ S.intersection s1 s2
evalSet "Set_cup" [VS s1, VS s2]
  = return $! VS $ S.union s1 s2
evalSet "Set_dif" [VS s1, VS s2]
  = return $! VS $ s1 S.\\ s2
evalSet "Set_sub" [VS s1, VS s2]
  = return $! VB $ S.isSubsetOf s1 s2
evalSet "Set_mem" [v, VS s]
  = return $! VB $ S.member v s
evalSet f es = throwM $ EvalError $ printf "evalSet(%s, %s)" (show f) (show es)

evalBody
  :: Language.Haskell.Liquid.Types.Def ty ctor
     -> [Val] -> M.HashMap Symbol Val -> Target Val
evalBody eq xs env = go $ body eq
  where
    go (E e) = evalExpr e env'
    go (P p) = evalPred p env' >>= \b -> return $ if b then VB True else VB False
    go (R v p) = do e <- evalRel v p env'
                    case e of
                      Nothing -> throwM $ EvalError $ "evalBody can't handle: " ++ show (R v p)
                      Just e  -> return e
    --go (R v (PBexp (EApp f e))) | val f == "Set_emp" = return $ app setSym []
    ----FIXME: figure out how to handle the general case..
    --go (R v p) = return (ECon (I 0))

    env' = M.union (M.fromList (zip (map fst (binds eq)) xs)) env
    -- su = mkSubst $ zip (map fst (binds eq)) xs

evalRel :: Symbol -> Expr -> M.HashMap Symbol Val -> Target (Maybe Val)
evalRel v (PAnd ps)       m = Just . head . catMaybes <$> sequence [evalRel v p m | p <- ps]
evalRel v (PImp p q)      m = do pv <- evalPred p m
                                 if pv
                                    then evalRel v q m
                                    else return Nothing
evalRel v (PAtom Eq (EVar v') e2) m
  | v == v'
  = Just <$> evalExpr e2 m
-- evalRel v (PBexp (EApp f [EVar v'])) _
evalRel v (EApp (EVar f) (EVar v')) _
  | v == v' && f == "Set_emp"
  = return $! Just $ VS S.empty
evalRel _ p               _
  = throwM $ EvalError $ "evalRel: " ++ show p


evalBop :: Bop -> Val -> Val -> Val
evalBop Plus  (VV (I x)) (VV (I y)) = VV . I $ x + y
evalBop Minus (VV (I x)) (VV (I y)) = VV . I $ x - y
evalBop Times (VV (I x)) (VV (I y)) = VV . I $ x * y
evalBop Div   (VV (I x)) (VV (I y)) = VV . I $ x `div` y
evalBop Mod   (VV (I x)) (VV (I y)) = VV . I $ x `mod` y
evalBop b     e1           e2       = error $ printf "evalBop(%s, %s, %s)" (show b) (show e1) (show e2)
