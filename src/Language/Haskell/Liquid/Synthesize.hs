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
import           Data.Graph (SCC(..))
import           Data.Maybe
import           Debug.Trace 
import           Language.Haskell.Liquid.GHC.TypeRep
import           Language.Haskell.Liquid.Synthesis
import           Data.List 
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
              -- let tt = fromJust $ M.lookup (symbol vErr) (reGlobal renv)
              -- trace (" [ FIND ] " ++ show tt ++ " haskell type " ++ showTy (exprType (GHC.Var vErr)) ++ " converted type " ++ showTy (toType tt)) $ 
              GHC.mkLams ys <$$> synthesizeBasic CaseSplit " Function " goalType
      where (_, (xs, txs, _), to) = bkArrow t 

-- TODO: Decide whether it is @CaseSplit@ or @TermGen@.
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
  -- if m == CaseSplit 
  --   then do senv <- getSEnv 
  --           lenv <- getLocalEnv
  --           es <- synthesizeMatch (" synthesizeMatch for t = " ++ show t ++ s) lenv senv t
  --           if null es then synthesizeBasic TermGen "" t else return es
  --   else do 
  es <- genTerms s t
  if null es  then do senv <- getSEnv
                      lenv <- getLocalEnv 
                      synthesizeMatch (" synthesizeMatch for t = " ++ show t ++ s) lenv senv t
              else return es

synthesizeMatch :: String -> LEnv -> SSEnv -> SpecType -> SM [CoreExpr]
synthesizeMatch s lenv γ t = do
  em <- getSEMem 
  let es0 = [((e, t, c), d) | ( t@(TyConApp c _), e, d ) <- em]
      es1 = filter (noPairLike . fst) es0
      es2 = sortOn snd es1
      es3 = map fst es2
  id <- incrCase es3
  if null es3 
    then return []
    else do let scrut = es3 !! id -- es !! id
            trace (" CaseSplit " ++ show (map (\x -> (fst3.fst $x, snd x)) es2) ++ " \n Scrutinee " ++ show (fst3 scrut)) $   
              withIncrDepth (matchOnExpr s t scrut)
              -- (es2, es3) = span (isVar . fst3 . fst) es1
              -- es4 = sortOn snd es2
              -- es5 = sortOn snd es3
            
            -- withIncrDepth (matchOn s t scrut)
            -- where es = [(v,t,rtc_tc c) | (x, (t@(RApp c _ _ _), v)) <- M.toList γ] 

noPairLike :: (GHC.CoreExpr, Type, TyCon) -> Bool
noPairLike (e, t, c) = 
  if length (tyConDataCons c) > 1 
    then True
    else inspect e (tyConDataCons c)

inspect :: GHC.CoreExpr -> [DataCon] -> Bool
inspect e [dataCon] 
  = not $ outer e == dataConWorkId dataCon
inspect _ _  
  = error " Should be a singleton. "

outer :: GHC.CoreExpr -> Var
outer (GHC.Var v)
  = v
outer (GHC.App e1 e2)
  = outer e1

isVar :: GHC.CoreExpr -> Bool
isVar (GHC.Var _) = True
isVar _ = False

matchOnExpr :: String -> SpecType -> (CoreExpr, Type, TyCon) -> SM [CoreExpr]
matchOnExpr s t (GHC.Var v, tx, c) 
  = matchOn s t (v, tx, c)
matchOnExpr s t (e, tx, c)
  = trace (" Match On Expr " ++ show e) $
      do  freshV <- freshVarType tx
          es <- matchOn s t (freshV, tx, c)
          return $ (GHC.Let (GHC.NonRec freshV e)) <$> es

matchOn :: String -> SpecType -> (Var, Type, TyCon) -> SM [CoreExpr]
matchOn s t (v, tx, c) =
  (GHC.Case (GHC.Var v) v tx <$$> sequence) <$> mapM (makeAlt s v t (v, tx)) (tyConDataCons c)


makeAlt :: String -> Var -> SpecType -> (Var, Type) -> DataCon -> SM [GHC.CoreAlt]
makeAlt s var t (x, tx@(TyConApp _ ts)) c = locally $ do -- (AltCon, [b], Expr b)
  ts <- liftCG $ mapM trueTy τs
  xs <- mapM freshVar ts    
  addsEnv $ zip xs ts 
  addsEmem $ zip xs ts 
  liftCG0 (\γ -> caseEnv γ x mempty (GHC.DataAlt c) xs Nothing)
  es <- synthesizeBasic TermGen (s ++ " makeAlt for " ++ show c ++ " with vars " ++ show xs) t
  return $ (\e -> (GHC.DataAlt c, xs, e)) <$> es
  where 
    (_, _, τs) = dataConInstSig (tracepp (" makeAlt for ts " ++ concat (map showTy ts)) c) ts -- (toType <$> ts)
makeAlt s _ _ _ _ = error $ "makeAlt.bad argument " ++ s