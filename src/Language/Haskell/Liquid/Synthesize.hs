{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Synthesize (
    synthesize
  ) where

import           Language.Haskell.Liquid.Types
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
import           Data.Tuple.Extra

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
          (senv1, foralls) = initSSEnv typeOfTopLvlBnd cginfo ssenv0
      
      ctx <- SMT.makeContext fcfg tgt
      state0 <- initState ctx fcfg cgi cge env topLvlBndr uniVars M.empty

      fills <- synthesize' tgt ctx fcfg cgi cge env senv1 x typeOfTopLvlBnd topLvlBndr typeOfTopLvlBnd foralls state0

      return $ ErrHole loc (
        if length fills > 0 
          then text "\n Hole Fills: " <+> pprintMany fills 
          else mempty) mempty (symbol x) t 


-- Assuming that @tx@ is the @SpecType@ of the top level variable. 
-- I thought I had it fixed...
synthesize' :: FilePath -> SMT.Context -> F.Config -> CGInfo -> CGEnv -> REnv -> SSEnv -> Var -> SpecType ->  Var -> SpecType -> [Var] -> SState -> IO [CoreExpr]
synthesize' tgt ctx fcfg cgi cge renv senv x tx xtop ttop foralls st2
 = evalSM (go tx) ctx tgt fcfg cgi cge renv senv st2
  where 

    go :: SpecType -> SM [CoreExpr]

    -- Type Abstraction 
    go (RAllT a t x)      = GHC.Lam (tyVarVar a) <$$> go t
          
    go t@(RApp c _ts _ r) = do  
      let coreProgram = giCbs $ giSrc $ ghcI cgi
          args  = drop 1 (argsP coreProgram xtop)
          (_, (xs, txs, _), _) = bkArrow ttop
      addEnv xtop $ decrType xtop ttop args (zip xs txs)

      -- Special Treatment for synthesis of integers 
      if R.isNumeric (tyConEmbed cgi) c
          then error " [ Numeric in synthesize ] Update liquid fixpoint. "
          else do let ts = unifyWith (toType t)
                  if null ts  then modify (\s -> s { sUGoalTy = Nothing } )
                              else modify (\s -> s { sUGoalTy = Just ts } )
                  modify (\s -> s {sForalls = (foralls, [])})
                  emem0 <- insEMem0 senv -- TODO Fix
                  modify (\s -> s { sExprMem = emem0 })
                  synthesizeBasic CaseSplit " Constructor " t

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
                  ts = unifyWith hsGoalTy
              if null ts  then modify (\s -> s { sUGoalTy = Nothing } )
                          else modify (\s -> s { sUGoalTy = Just ts } )
              modify (\s -> s { sForalls = (foralls, []) } )
              emem0 <- insEMem0 senv1
              modify (\s -> s { sExprMem = emem0 })
              vErr <- varError 
              let tt = fromJust $ M.lookup (symbol vErr) (reGlobal renv)
              trace (" [ FIND ] " ++ show tt ++ " haskell type " ++ showTy (exprType (GHC.Var vErr)) ++ " converted type " ++ showTy (toType tt)) $ 
                GHC.mkLams ys <$$> synthesizeBasic CaseSplit " Function " goalType
      where (_, (xs, txs, _), to) = bkArrow t 

data Mode 
  = CaseSplit -- ^ First case split and then generate terms.
  | TermGen   -- ^ First generate terms and then case split.
  deriving Eq

synthesizeBasic :: Mode -> String -> SpecType -> SM [CoreExpr]
synthesizeBasic m s t = do
  senv <- getSEnv
  let ts = unifyWith (toType t) -- ^ All the types that are used for instantiation.
  if null ts  then  modify (\s -> s { sUGoalTy = Nothing } )
              else  modify (\s -> s { sUGoalTy = Just ts } )
  fixEMem t
  if m == CaseSplit 
    then do senv <- getSEnv 
            lenv <- getLocalEnv
            synthesizeMatch (" synthesizeMatch for t = " ++ show t ++ s) lenv senv t
    else do 
      es <- genTerms s t
      if null es  then do senv <- getSEnv
                          lenv <- getLocalEnv 
                          synthesizeMatch (" synthesizeMatch for t = " ++ show t ++ s) lenv senv t
                  else return es

synthesizeMatch :: String -> LEnv -> SSEnv -> SpecType -> SM [CoreExpr]
synthesizeMatch s lenv γ t = do
  em <- getSEMem 
  let es0 = [(e, t, c) | ( t@(TyConApp c _), e, _ ) <- em]
  id <- incrCase es
  let scrut = es !! id
      b x y = thd3 x == thd3 y
      es1 = groupBy b es0
  trace (" CaseSplit " ++ show (fst3 scrut)) $ withIncrDepth (matchOn s t scrut)
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
  es <- synthesizeBasic TermGen (s ++ " makeAlt for " ++ show c ++ " with vars " ++ show xs) t
  return $ (\e -> (GHC.DataAlt c, xs, e)) <$> es
  where 
    (_, _, τs) = dataConInstSig c (toType <$> ts)
makeAlt s _ _ _ _ = error $ "makeAlt.bad argument " ++ s
