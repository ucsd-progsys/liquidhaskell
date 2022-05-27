{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Haskell.Liquid.Synthesize (
    synthesize
  ) where

import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Generate 
import qualified Language.Haskell.Liquid.Types.RefType as R
import           Language.Haskell.Liquid.Synthesize.Termination
import           Language.Haskell.Liquid.Synthesize.Generate
import           Language.Haskell.Liquid.Synthesize.GHC hiding (SSEnv)
import           Language.Haskell.Liquid.Synthesize.Monad
import           Language.Haskell.Liquid.Synthesize.Misc hiding (notrace)
import           Language.Haskell.Liquid.Constraint.Fresh (trueTy)
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Types hiding (SEnv, SVar, Error)
import qualified Language.Fixpoint.Types        as F 
import qualified Language.Fixpoint.Types.Config as F
import           Language.Haskell.Liquid.Synthesize.Env
import           Language.Haskell.Liquid.GHC.API as GHC hiding (text, ($+$))

import           Text.PrettyPrint.HughesPJ (text, ($+$))
import           Control.Monad.State.Lazy
import qualified Data.HashMap.Strict as M 
import           Data.Maybe

synthesize :: FilePath -> F.Config -> CGInfo -> IO [Error]
synthesize tgt fcfg cginfo = 
  mapM go (M.toList $ holesMap cginfo)
  where 
    measures = map (val . msName) ((gsMeasures . gsData . giSpec . ghcI) cginfo)
    go (x, HoleInfo _ loc env (cgi,cge)) = do 
      let topLvlBndr = fromMaybe (error "Top-level binder not found") (cgVar cge)
          typeOfTopLvlBnd = fromMaybe (error "Type: Top-level symbol not found") (M.lookup (symbol topLvlBndr) (reGlobal env))
          coreProgram = giCbs $ giSrc $ ghcI cgi
          (uniVars, _) = getUniVars coreProgram topLvlBndr
          fromREnv' = filterREnv (reLocal env)
          fromREnv'' = M.fromList (filter (rmClassVars . toType False . snd) (M.toList fromREnv'))
          rmClassVars t = case t of { TyConApp c _ -> not . isClassTyCon $ c; _ -> True }
          fromREnv  = M.fromList (rmMeasures measures (M.toList fromREnv''))
          isForall t = case t of { ForAllTy{} -> True; _ -> False}
          rEnvForalls = M.fromList (filter (isForall . toType False . snd) (M.toList fromREnv))
          fs = map (snd . snd) $ M.toList (symbolToVar coreProgram topLvlBndr rEnvForalls)

          ssenv0 = symbolToVar coreProgram topLvlBndr fromREnv
          (senv1, foralls') = initSSEnv typeOfTopLvlBnd cginfo ssenv0
      
      ctx <- SMT.makeContext fcfg tgt
      state0 <- initState ctx fcfg cgi cge env topLvlBndr (reverse uniVars) M.empty
      let foralls = foralls' ++ fs
      fills <- synthesize' ctx cgi senv1 typeOfTopLvlBnd topLvlBndr typeOfTopLvlBnd foralls state0

      return $ ErrHole loc (
        if not (null fills)
          then text "\n Hole Fills:" $+$ pprintMany (map (coreToHs typeOfTopLvlBnd topLvlBndr . fromAnf) fills)
          else mempty) mempty (symbol x) typeOfTopLvlBnd 


synthesize' :: SMT.Context -> CGInfo -> SSEnv -> SpecType ->  Var -> SpecType -> [Var] -> SState -> IO [CoreExpr]
synthesize' ctx cgi ssenv tx xtop ttop foralls st2
 = evalSM (go tx) ctx ssenv st2
  where 

    go :: SpecType -> SM [CoreExpr]

    -- Type Abstraction 
    go (RAllT a t _x)      = GHC.Lam (tyVarVar a) <$$> go t
          
    go t@(RApp c _ts _ _r) = do  
      let coreProgram = giCbs $ giSrc $ ghcI cgi
          args  = drop 1 (argsP coreProgram xtop)
          (_, (xs, _, txs, _), _) = bkArrow ttop
      addEnv xtop $ decrType xtop ttop args (zip xs txs)

      if R.isNumeric (tyConEmbed cgi) c
          then error " [ Numeric in synthesize ] Update liquid fixpoint. "
          else do let ts = unifyWith (toType False t)
                  if null ts  then modify (\s -> s { sUGoalTy = Nothing } )
                              else modify (\s -> s { sUGoalTy = Just ts } )
                  modify (\s -> s {sForalls = (foralls, [])})
                  emem0 <- insEMem0 ssenv
                  modify (\s -> s { sExprMem = emem0 })
                  synthesizeBasic t

    go (RAllP _ t) = go t

    go (RRTy _env _ref _obl t) = go t

    go t@RFun{} 
         = do ys <- mapM freshVar txs
              let su = F.mkSubst $ zip xs (EVar . symbol <$> ys) 
              mapM_ (uncurry addEnv) (zip ys ((subst su)<$> txs)) 
              let dt = decrType xtop ttop ys (zip xs txs)
              addEnv xtop dt 
              mapM_ (uncurry addEmem) (zip ys (subst su <$> txs)) 
              addEmem xtop dt
              senv1 <- getSEnv
              let goalType' = subst su to
                  hsGoalTy = toType False goalType'
                  ts = unifyWith hsGoalTy
              if null ts  then modify (\s -> s { sUGoalTy = Nothing } )
                          else modify (\s -> s { sUGoalTy = Just ts } )
              modify (\s -> s { sForalls = (foralls, []) } )
              emem0 <- insEMem0 senv1
              modify (\s -> s { sExprMem = emem0 })
              mapM_ (\y -> addDecrTerm y []) ys
              scruts <- synthesizeScrut ys
              modify (\s -> s { scrutinees = scruts })
              GHC.mkLams ys <$$> synthesizeBasic goalType'
      where (_, (xs, _,txs, _), to) = bkArrow t 

    go t = error (" Unmatched t = " ++ show t)

synthesizeBasic :: SpecType -> SM [CoreExpr]
synthesizeBasic t = do
  let ts = unifyWith (toType False t) -- All the types that are used for instantiation.
  if null ts  then  modify (\s -> s { sUGoalTy = Nothing } )
              else  modify (\s -> s { sUGoalTy = Just ts } )
  modify (\s -> s { sGoalTys = [] })
  fixEMem t
  es <- genTerms t
  if null es  then synthesizeMatch t
              else return es

synthesizeMatch :: SpecType -> SM [CoreExpr]
synthesizeMatch t = do
  scruts <- scrutinees <$> get
  i <- incrCase 
  case safeIxScruts i scruts of
    Nothing  ->  return []
    Just id' ->  if null scruts
                  then return []
                  else withIncrDepth (matchOnExpr t (scruts !! id'))

synthesizeScrut :: [Var] -> SM [(CoreExpr, Type, TyCon)]
synthesizeScrut vs = do
  exprs <- synthesizeScrutinee vs
  let exprs' = map (\e -> (exprType e, e)) exprs
      isDataCon v = case varType v of { TyConApp c _ -> not . isClassTyCon $ c; _ -> False }
      vs0 = filter isDataCon vs
      es0 = map GHC.Var vs0 
      es1 = map (\e -> (exprType e, e)) es0
      es2 = [(e, t, c) | (t@(TyConApp c _), e) <- es1]
  return (es2 ++ [(e, t, c) | (t@(TyConApp c _), e) <- exprs'])

matchOnExpr :: SpecType -> (CoreExpr, Type, TyCon) -> SM [CoreExpr]
matchOnExpr t (GHC.Var v, tx, c) 
  = matchOn t (v, tx, c)
matchOnExpr t (e, tx, c)
  = do  freshV <- freshVarType tx
        freshSpecTy <- liftCG $ (trueTy False) tx
        -- use consE
        addEnv freshV freshSpecTy
        es <- matchOn t (freshV, tx, c)
        return $ GHC.Let (GHC.NonRec freshV e) <$> es

matchOn :: SpecType -> (Var, Type, TyCon) -> SM [CoreExpr]
matchOn t (v, tx, c) =
  (GHC.Case (GHC.Var v) v tx <$$> sequence) <$> mapM (makeAlt t (v, tx)) (tyConDataCons c)


makeAlt :: SpecType -> (Var, Type) -> DataCon -> SM [GHC.CoreAlt]
makeAlt t (x, TyConApp _ kts) c = locally $ do
  ts <- liftCG $ mapM (trueTy False) τs
  xs <- mapM freshVar ts
  newScruts <- synthesizeScrut xs
  modify (\s -> s { scrutinees = scrutinees s ++ newScruts } )
  addsEnv $ zip xs ts
  addsEmem $ zip xs ts
  addDecrTerm x xs
  liftCG0 (\γ -> caseEnv γ x mempty (GHC.DataAlt c) xs Nothing)
  es <- synthesizeBasic t
  return $ (GHC.DataAlt c, xs, ) <$> es
  where 
    (_, _, τs) = dataConInstSig c kts
makeAlt _ _ _ = error "makeAlt.bad argument "
