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
import           Language.Haskell.Liquid.Synthesize.GHC hiding (SSEnv)
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
import           DynFlags 
import           MkCore
import           Language.Haskell.Liquid.GHC.Play (isHoleVar)


-- containt GHC primitives
-- JP: Should we get this from REnv instead?
-- TODO: Get the constructors from REnv.
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
          typeOfTopLvlBnd = fromMaybe (error "Type: Top-level symbol not found") (M.lookup (symbol topLvlBndr) (reGlobal env))
          coreProgram = giCbs $ giSrc $ ghcI cgi
          ssenv0 = symbolToVar coreProgram topLvlBndr (filterREnv (reLocal env) topLvlBndr)
          senv1 = initSSEnv cginfo ssenv0
      
      ctx <- SMT.makeContext fcfg tgt
      state0 <- initState ctx fcfg cgi cge env M.empty
      fills <- map fromAnf <$> synthesize' tgt ctx fcfg cgi cge env senv1 x t topLvlBndr typeOfTopLvlBnd state0

      return $ ErrHole loc (
        if length fills > 0 
          then text "\n Hole Fills: " <+> pprintMany fills 
          else mempty) mempty (symbol x) t 


synthesize' :: FilePath -> SMT.Context -> F.Config -> CGInfo -> CGEnv -> REnv -> SSEnv -> Var -> SpecType ->  Var -> SpecType -> SState -> IO [CoreExpr]
synthesize' tgt ctx fcfg cgi cge renv senv x tx xtop ttop st2
 = evalSM (go tx) ctx tgt fcfg cgi cge renv senv st2
  where 

    go :: SpecType -> SM [CoreExpr]

    -- Type Abstraction 
    go (RAllT a t)       = GHC.Lam (tyVarVar a) <$$> go t
          
    go t@(RApp c _ts _ r) = do  
      let coreProgram = giCbs $ giSrc $ ghcI cgi
          args  = case argsP coreProgram xtop of { [] -> []; (_ : xs) -> xs }
          (_, (xs, txs, _), _) = bkArrow ttop
      addEnv xtop $ fst $ decrType xtop ttop args (zip xs txs)
      if R.isNumeric (tyConEmbed cgi) c
          -- Special Treatment for synthesis of integers          
          then do let RR s (Reft(x,rr)) = rTypeSortedReft (tyConEmbed cgi) t 
                  ctx <- sContext <$> get 
                  liftIO $ SMT.smtPush ctx
                  liftIO $ SMT.smtDecl ctx x s
                  liftIO $ SMT.smtCheckSat ctx rr 
                  -- Get model and parse the value of x
                  SMT.Model modelBinds <- liftIO $ SMT.smtGetModel ctx
                  
                  let xNotFound = error $ "Symbol " ++ show x ++ "not found."
                      smtVal = T.unpack $ fromMaybe xNotFound $ lookup x modelBinds

                  liftIO (SMT.smtPop ctx)
                  filterM (hasType t) [mkIntExpr unsafeGlobalDynFlags (read smtVal :: Integer)] -- TODO: TypeCheck 
          else do
            emem0 <- withInsInitEM senv 
            modify (\s -> s { sExprMem = emem0 })
            synthesizeBasic t

    go t = do ys <- mapM freshVar txs
              let su = F.mkSubst $ zip xs ((EVar . symbol) <$> ys) 
              mapM_ (uncurry addEnv) (zip ys ((subst su)<$> txs)) 
              let (dt, b) = decrType xtop ttop ys (zip xs txs)
              addEnv xtop dt
              emem0 <- withInsInitEM senv 
              modify (\s -> s { sExprMem = emem0 }) 
              mapM_ (uncurry addEmem) (zip ys ((subst su)<$> txs)) 
              addEmem xtop dt
              GHC.mkLams ys <$$> synthesizeBasic (subst su to) 
      where (_, (xs, txs, _), to) = bkArrow t 

synthesizeBasic :: SpecType -> SM [CoreExpr]
synthesizeBasic t = do
  let ht     = toType t
      tyvars = varsInType ht
  case tyvars of
    []  -> modify (\s -> s { sGoalTyVar = Nothing})
    [x] -> modify (\s -> s { sGoalTyVar = Just x })
    _   -> error errorMsg
      where errorMsg = "TyVars in type [" ++ show t ++ "] are more than one ( " ++ show tyvars ++ " )." 
  es <- genTerms t
  case es of 
    [] -> do
      senv <- getSEnv
      lenv <- getLocalEnv 
      synthesizeMatch lenv senv t
    _  -> return es


synthesizeMatch :: LEnv -> SSEnv -> SpecType -> SM [CoreExpr]
synthesizeMatch lenv γ t = -- trace ("[synthesizeMatch] es = " ++ show es) $ 
  join <$> mapM (withIncrDepth . matchOn t) es
  where es = [(v,t,rtc_tc c) | (x, (t@(RApp c _ _ _), v)) <- M.toList γ] 


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
  return $ (\e -> (GHC.DataAlt c, xs, e)) <$> es
  where 
    (_, _, τs) = dataConInstSig c (toType <$> ts)
makeAlt _ _ _ _ = error "makeAlt.bad argument"
    


