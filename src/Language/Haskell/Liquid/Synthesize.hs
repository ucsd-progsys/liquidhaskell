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
import           Language.Haskell.Liquid.Synthesize.Misc hiding (notrace)
import           Language.Haskell.Liquid.Constraint.Fresh (trueTy)
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Types hiding (SEnv, SVar, Error)
import qualified Language.Fixpoint.Types        as F 
import qualified Language.Fixpoint.Types.Config as F
import           Language.Haskell.Liquid.Synthesize.Env

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
import qualified Data.HashSet as S
import           Data.Default 
import           Data.Graph (SCC(..))
import qualified Data.Text as T
import           Data.Maybe
import           Debug.Trace 
import           Language.Haskell.Liquid.GHC.TypeRep
import           Language.Haskell.Liquid.Synthesis
import           Data.List 
import           Literal
import           Language.Haskell.Liquid.GHC.Play (isHoleVar)
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Haskell.Liquid.Synthesize.Classes

synthesize :: FilePath -> F.Config -> CGInfo -> IO [Error]
synthesize tgt fcfg cginfo = 
  mapM goSCC $ holeDependencySSC $ holesMap cginfo
  where 
    goSCC (AcyclicSCC v) = go v
    goSCC (CyclicSCC []) = error "synthesize goSCC: unreachable"
    goSCC (CyclicSCC vs@((_, HoleInfo{..}):_)) = return $ ErrHoleCycle hloc $ map (symbol . fst) vs

    go (x, HoleInfo t loc env (cgi,cge)) = do 
      let topLvlBndr = fromMaybe (error "Top-level binder not found") (cgVar cge)
          typeOfTopLvlBnd = fromMaybe (error "Type: Top-level symbol not found") (M.lookup (symbol topLvlBndr) (reGlobal env))
          coreProgram = giCbs $ giSrc $ ghcI cgi
          uniVars = getUniVars coreProgram topLvlBndr
          ssenv0 = symbolToVar coreProgram topLvlBndr (filterREnv (reLocal env) topLvlBndr)
          senv1 = initSSEnv typeOfTopLvlBnd cginfo ssenv0
      
      ctx <- SMT.makeContext fcfg tgt
      state0 <- initState ctx fcfg cgi cge env topLvlBndr uniVars M.empty

      fills <- synthesize' tgt ctx fcfg cgi cge env senv1 x typeOfTopLvlBnd topLvlBndr typeOfTopLvlBnd state0

      return $ ErrHole loc (
        if length fills > 0 
          then text "\n Hole Fills: " <+> pprintMany fills 
          else mempty) mempty (symbol x) t 


-- Assuming that @tx@ is the @SpecType@ of the top level variable. I thought I had it fixed...
synthesize' :: FilePath -> SMT.Context -> F.Config -> CGInfo -> CGEnv -> REnv -> SSEnv -> Var -> SpecType ->  Var -> SpecType -> SState -> IO [CoreExpr]
synthesize' tgt ctx fcfg cgi cge renv senv x tx xtop ttop st2
 = evalSM (go tx) ctx tgt fcfg cgi cge renv senv st2
  where 

    go :: SpecType -> SM [CoreExpr]

    -- Type Abstraction 
    go (RAllT a t x)      = GHC.Lam (tyVarVar a) <$$> go t
          
    go t@(RApp c _ts _ r) = do  
      let coreProgram = giCbs $ giSrc $ ghcI cgi
          args  = case argsP coreProgram xtop of { [] -> []; (_ : xs) -> xs }
          (_, (xs, txs, _), _) = bkArrow ttop
      addEnv xtop $ decrType xtop ttop args (zip xs txs)

      -- Special Treatment for synthesis of integers 
      if R.isNumeric (tyConEmbed cgi) c
          then error " [ Numeric in synthesize ] Update liquid fixpoint. "
          else do emem0 <- withInsInitEM senv 
                  modify (\s -> s { sExprMem = emem0 })
                  synthesizeBasic " Constructor " t

    go t = do ys <- mapM freshVar txs
              let su = F.mkSubst $ zip xs ((EVar . symbol) <$> ys) 
              mapM_ (uncurry addEnv) (zip ys ((subst su)<$> txs)) 
              let dt = decrType xtop ttop ys (zip xs txs)
              addEnv xtop dt 
              mapM_ (uncurry addEmem) (zip ys ((subst su)<$> txs)) 
              addEmem xtop dt
              senv1 <- getSEnv
              let goalType = subst su to
                  hsGoalTy = toType goalType 
                  tvs = varsInType hsGoalTy
              case tvs of
                [] -> modify (\s -> s { sGoalTyVar = Nothing})
                _  -> modify (\s -> s { sGoalTyVar = Just tvs })
              emem0 <- withInsInitEM senv1
              modify (\s -> s { sExprMem = emem0 })
              emem1 <- getSEMem
              trace (" ExpressionMemory " ++ showEmem emem1) $ GHC.mkLams ys <$$> synthesizeBasic " Function " goalType
      where (_, (xs, txs, _), to) = bkArrow t 

synthesizeBasic :: String -> SpecType -> SM [CoreExpr]
synthesizeBasic s t = do
  senv <- getSEnv
  let ht  = toType t
      tvs = varsInType ht
  case tvs of
    [] -> modify (\s -> s { sGoalTyVar = Nothing})
    _  -> modify (\s -> s { sGoalTyVar = Just tvs })
  es <- genTerms s t
  case es of 
    [] -> do  senv <- getSEnv
              lenv <- getLocalEnv 
              synthesizeMatch (" synthesizeMatch for t = " ++ show t) lenv senv t
    es0  -> return es0


synthesizeMatch :: String -> LEnv -> SSEnv -> SpecType -> SM [CoreExpr]
synthesizeMatch s lenv γ t = 
  join <$> mapM (withIncrDepth . matchOn s t) es
  where es = [(v,t,rtc_tc c) | (x, (t@(RApp c _ _ _), v)) <- M.toList γ] 


matchOn :: String -> SpecType -> (Var, SpecType, TyCon) -> SM [CoreExpr]
matchOn s t (v, tx, c) =
  (GHC.Case (GHC.Var v) v (toType tx) <$$> sequence) <$> mapM (makeAlt s v t (v, tx)) (tyConDataCons c)


makeAlt :: String -> Var -> SpecType -> (Var, SpecType) -> DataCon -> SM [GHC.CoreAlt]
makeAlt s var t (x, tx@(RApp _ ts _ _)) c = locally $ do -- (AltCon, [b], Expr b)
  ts <- liftCG $ mapM trueTy τs
  xs <- mapM freshVar ts    
  addsEnv $ zip xs ts 
  addsEmem $ zip xs ts 
  liftCG0 (\γ -> caseEnv γ x mempty (GHC.DataAlt c) xs Nothing)
  es <- synthesizeBasic (s ++ " makeAlt for " ++ show c ++ " with vars " ++ show xs) t
  return $ (\e -> (GHC.DataAlt c, xs, e)) <$> es
  where 
    (_, _, τs) = dataConInstSig c (toType <$> ts)
makeAlt s _ _ _ _ = error $ "makeAlt.bad argument " ++ s


---- Move them ------------
instance PPrint GHC.AltCon

showCoreAlt :: GHC.CoreAlt -> String
showCoreAlt (GHC.DataAlt altCon, vars, expr) = 
  " For " ++ show altCon ++ " vars " ++ show vars ++ " expr " ++ show expr
showCoreAlt _ = " No! "

showCoreAlts :: [GHC.CoreAlt] -> String
showCoreAlts alts = concat (map showCoreAlt alts)
