{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module Language.Haskell.Liquid.Synthesize (
    synthesize
  ) where

import           Language.Haskell.Liquid.Types hiding (SVar)
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Generate 
import           Language.Haskell.Liquid.Constraint.Env 
import qualified Language.Haskell.Liquid.Types.RefType as R
import           Language.Haskell.Liquid.GHC.Misc (showPpr)
import           Language.Haskell.Liquid.Synthesize.Termination
import           Language.Haskell.Liquid.Synthesize.Generate
import           Language.Haskell.Liquid.Synthesize.GHC
import           Language.Haskell.Liquid.Synthesize.Check
import           Language.Haskell.Liquid.Synthesize.Monad
import           Language.Haskell.Liquid.Synthesize.Misc
import           Language.Haskell.Liquid.Constraint.Fresh (trueTy)
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Types hiding (SEnv, SVar, Error)
import qualified Language.Fixpoint.Types        as F 
import qualified Language.Fixpoint.Types.Config as F

import CoreUtils (exprType)
import CoreSyn (CoreExpr)
import qualified CoreSyn as GHC
import Var 
import TyCon
import DataCon
import TysWiredIn
import qualified TyCoRep as GHC 
import           Text.PrettyPrint.HughesPJ ((<+>), text, char, Doc, vcat, ($+$))

import           Control.Monad.State.Lazy
import qualified Data.HashMap.Strict as M 
import           Data.Default 
import           Data.Graph (SCC(..))
import qualified Data.Text as T
import           Data.Maybe
import           Debug.Trace 
import           Language.Haskell.Liquid.GHC.TypeRep
import           Language.Haskell.Liquid.Synthesis
import           Data.List 
import           Literal

notrace :: String -> a -> a 
notrace _ a = a 

-- containt GHC primitives
-- JP: Should we get this from REnv instead?
initSSEnv :: CGInfo -> SSEnv -> SSEnv
initSSEnv info senv = M.union senv (M.fromList (filter iNeedIt (mkElem <$> prims)))
  where
    mkElem (v, lt) = (F.symbol v, (val lt, v))
    prims = gsCtors $ gsData $ giSpec $ ghcI info
    iNeedIt (_, (_, v)) = v `elem` (dataConWorkId <$> [ nilDataCon, consDataCon ]) 



synthesize :: FilePath -> F.Config -> CGInfo -> IO [Error]
synthesize tgt fcfg cginfo = mapM goSCC $ holeDependencySSC $ holesMap cginfo -- TODO: foldM filled holes to dependencies. XXX
  where 
    goSCC (AcyclicSCC v) = go v
    goSCC (CyclicSCC []) = error "synthesize goSCC: unreachable"
    goSCC (CyclicSCC vs@((_, HoleInfo{..}):_)) = return $ ErrHoleCycle hloc $ map (symbol . fst) vs

    go (x, HoleInfo t loc env (cgi,cge)) = do 
      let topLvlBndr = fromMaybe (error "Top-level binder not found") (cgVar cge)
          -- We also need to generate its type for non-termination check.
          typeOfTopLvlBnd = fromMaybe (error "Type: Top-level symbol not found") (M.lookup (symbol topLvlBndr) (reGlobal env))
          (_, (xs, txs, _), to) = bkArrow t
      ctx <- SMT.makeContext fcfg tgt
      state0 <- initState ctx fcfg cgi cge env M.empty

      -- (ys, st1) <- runStateT (mapM freshVar txs) state0
      -- let su = F.mkSubst $ zip xs ((EVar . symbol) <$> ys)
      -- ((), st2) <- (mapM_ (uncurry addEnv) (zip ys ((subst su)<$> txs))) st1
      -- ((), st3) <- runStateT (addEnv topLvlBndr $ decrType topLvlBndr typeOfTopLvlBnd ys (zip xs txs)) st2
      -- let senv0 = ssEnv st3

      let senv1 = initSSEnv cginfo M.empty
          senv2 = M.insert (symbol topLvlBndr) (typeOfTopLvlBnd, topLvlBndr) senv1
      fills <- synthesize' tgt ctx fcfg cgi cge env senv2 x t state0

      -- SMT.cleanupContext ctx
      return $ ErrHole loc (
        if length fills > 0 
          then text "\n Hole Fills: " <+> pprintMany fills 
          else mempty) mempty (symbol x) t 


synthesize' :: FilePath -> SMT.Context -> F.Config -> CGInfo -> CGEnv -> REnv -> SSEnv -> Var -> SpecType -> SState -> IO [CoreExpr]
synthesize' tgt ctx fcfg cgi cge renv senv x tx st2 = evalSM (go tx) ctx tgt fcfg cgi cge renv senv st2
  where 

    go :: SpecType -> SM [CoreExpr] -- JP: [SM CoreExpr] ???

    -- Type Abstraction 
    go (RAllT a t)       = GHC.Lam (tyVarVar a) <$$> go t
          
    -- Special Treatment for synthesis of integers          
    go t@(RApp c _ts _ r)  
      | R.isNumeric (tyConEmbed cgi) c = 
          do  let RR s (Reft(x,rr)) = rTypeSortedReft (tyConEmbed cgi) t 
              ctx <- sContext <$> get 
              liftIO $ SMT.smtPush ctx
              liftIO $ SMT.smtDecl ctx x s
              liftIO $ SMT.smtCheckSat ctx rr 
              -- Get model and parse the value of x
              SMT.Model modelBinds <- liftIO $ SMT.smtGetModel ctx
              
              let xNotFound = error $ "Symbol " ++ show x ++ "not found."
                  smtVal = T.unpack $ fromMaybe xNotFound $ lookup x modelBinds

              liftIO (SMT.smtPop ctx)
              return [GHC.Lit (mkMachInt64 (read smtVal :: Integer))]


    go t = do ys <- mapM freshVar txs
              let su = F.mkSubst $ zip xs ((EVar . symbol) <$> ys) 
              mapM_ (uncurry addEnv) (zip ys ((subst su)<$> txs)) 
              mapM_ (uncurry addEmem) (zip ys ((subst su)<$> txs)) 
              addEnv x $ decrType x tx ys (zip xs txs)
              addEmem x $ decrType x tx ys (zip xs txs)
              GHC.mkLams ys <$$> synthesizeBasic (subst su to) 
      where (_, (xs, txs, _), to) = bkArrow t 

    

synthesizeBasic :: SpecType -> SM [CoreExpr]
synthesizeBasic t = {- trace ("[ synthesizeBasic ] goalType " ++ show t) $ -} do
  let ht     = toType t
      tyvars = varsInType ht
  case tyvars of
    []  -> modify (\s -> s { sGoalTyVar = Nothing})
    [x] -> modify (\s -> s { sGoalTyVar = Just x })
    _   -> error $ "TyVars in type [" ++ show t ++ "] are more than one ( " ++ show tyvars ++ " )."
  es <- genTerms t
  filterElseM (hasType t) es $ trace (" ty-vars " ++ show tyvars) $ do
    senv <- getSEnv
    lenv <- getLocalEnv 
    es' <- synthesizeMatch lenv senv t
    cgenv <- sCGEnv <$> get
    filterM (hasType t) es'


-- Panagiotis TODO: here I only explore the first one                     
--  We need the most recent one
synthesizeMatch :: LEnv -> SSEnv -> SpecType -> SM [CoreExpr]
synthesizeMatch lenv γ t 
  -- | [] <- es 
  -- = return def

  -- | otherwise 
  -- = maybe def id <$> monadicFirst 
  = trace ("[synthesizeMatch] es = " ++ show es) $ 
      join <$> mapM (withIncrDepth . matchOn t) (es <> ls)

  where 
    es = [(v,t,rtc_tc c) | (x, (t@(RApp c _ _ _), v)) <- M.toList γ] 
    ls = [(v,t,rtc_tc c) | (s, t@(RApp c _ _ _)) <- M.toList lenv
                         , Just v <- [symbolToVar s] -- JP: Is there better syntax for this?
         ]
    
    symbolToVar :: Symbol -> Maybe Var
    symbolToVar _ = Nothing -- TODO: Actually implement me!!! Dependent on abstract symbols? XXX
        
        -- -- Return first nonempty result.
        -- -- JP: probably want to keep going up to some limit of N results.
        -- monadicFirst :: (a -> m (Maybe b)) -> [a] -> m (Maybe b)
        -- monadicFirst _f [] = 
        --     return Nothing
        -- monadicFirst f (m:ms) = do
        --     mb <- f m
        --     case mb of
        --         r@(Just _) -> return r
        --         Nothing -> monadicFirst f ms


matchOn :: SpecType -> (Var, SpecType, TyCon) -> SM [CoreExpr]
matchOn t (v, tx, c) = (GHC.Case (GHC.Var v) v (toType tx) <$$> sequence) <$> mapM (makeAlt scrut t (v, tx)) (tyConDataCons c)
  where scrut = v
  -- JP: Does this need to be a foldM? Previous pattern matches could influence expressions of later patterns?



makeAlt :: Var -> SpecType -> (Var, SpecType) -> DataCon -> SM [GHC.CoreAlt]
makeAlt var t (x, tx@(RApp _ ts _ _)) c = locally $ do -- (AltCon, [b], Expr b)
  ts <- liftCG $ mapM trueTy τs
  xs <- mapM freshVar ts    
  addsEnv $ zip xs ts 
  addsEmem $ zip xs ts 
  liftCG0 (\γ -> caseEnv γ x mempty (GHC.DataAlt c) xs Nothing)
  es <- synthesizeBasic t
  -- es <- genTerms t
  return $ (\e -> (GHC.DataAlt c, xs, e)) <$> es
  where 
    (_, _, τs) = dataConInstSig c (toType <$> ts)
makeAlt _ _ _ _ = error "makeAlt.bad argument"
    


