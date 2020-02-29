{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}

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

import           CoreSyn (CoreExpr)
import qualified CoreSyn as GHC
import           Var 
import           TyCon
import           DataCon
import           Text.PrettyPrint.HughesPJ ((<+>), text)
import           Control.Monad.State.Lazy
import qualified Data.HashMap.Strict as M 
import           Data.Maybe
import           Debug.Trace 
import           Language.Haskell.Liquid.GHC.TypeRep
import           Data.List 
import           Data.Tuple.Extra

rmMeasures :: [Symbol] -> [(Symbol, SpecType)] -> [(Symbol, SpecType)]
rmMeasures _    [ ]         = [ ]
rmMeasures meas ((s, t):γs) = 
  case find (==s) meas of 
    Nothing -> (s, t) : rmMeasures meas γs
    Just _  -> rmMeasures meas γs

synthesize :: FilePath -> F.Config -> CGInfo -> IO [Error]
synthesize tgt fcfg cginfo = 
  mapM go (M.toList $ holesMap cginfo)
  where 
    measures = map (val . msName) ((gsMeasures . gsData . giSpec . ghcI) cginfo)
    go (x, HoleInfo t loc env (cgi,cge)) = do 
      let topLvlBndr = fromMaybe (error "Top-level binder not found") (cgVar cge)
          typeOfTopLvlBnd = fromMaybe (error "Type: Top-level symbol not found") (M.lookup (symbol topLvlBndr) (reGlobal env))
          coreProgram = giCbs $ giSrc $ ghcI cgi
          (uniVars, _) = getUniVars coreProgram topLvlBndr
          fromREnv' = filterREnv (reLocal env)
          fromREnv  = M.fromList (rmMeasures measures (M.toList fromREnv'))
          ssenv0 = symbolToVar coreProgram topLvlBndr fromREnv
          (senv1, foralls) = initSSEnv typeOfTopLvlBnd cginfo ssenv0
      
      ctx <- SMT.makeContext fcfg tgt
      state0 <- initState ctx fcfg cgi cge env topLvlBndr (reverse uniVars) M.empty

      fills <- synthesize' ctx cgi senv1 typeOfTopLvlBnd topLvlBndr typeOfTopLvlBnd foralls state0

      return $ ErrHole loc (
        if not (null fills)
          then text "\n Hole Fills: " <+> pprintMany fills
          else mempty) mempty (symbol x) t 


-- Assuming that @tx@ is the @SpecType@ of the top level variable. 
-- I thought I had it fixed...
synthesize' :: SMT.Context -> CGInfo -> SSEnv -> SpecType ->  Var -> SpecType -> [Var] -> SState -> IO [CoreExpr]
synthesize' ctx cgi senv tx xtop ttop foralls st2
 = evalSM (go tx) ctx senv st2
  where 

    go :: SpecType -> SM [CoreExpr]

    -- Type Abstraction 
    go (RAllT a t x)      = GHC.Lam (tyVarVar a) <$$> go t
          
    go t@(RApp c _ts _ _r) = do  
      let coreProgram = giCbs $ giSrc $ ghcI cgi
          args  = drop 1 (argsP coreProgram xtop)
          (_, (xs, txs, _), _) = bkArrow ttop
      addEnv xtop $ decrType xtop ttop args (zip xs txs)

      if R.isNumeric (tyConEmbed cgi) c
          then error " [ Numeric in synthesize ] Update liquid fixpoint. "
          else do let ts = unifyWith (toType t)
                  if null ts  then modify (\s -> s { sUGoalTy = Nothing } )
                              else modify (\s -> s { sUGoalTy = Just ts } )
                  modify (\s -> s {sForalls = (foralls, [])})
                  emem0 <- insEMem0 senv -- TODO Fix
                  modify (\s -> s { sExprMem = emem0 })
                  synthesizeBasic CaseSplit " Constructor " t

    go (RAllP _ t) = go t

    go (RRTy _env _ref _obl t) = go t

    go t@RFun{} 
         = do ys <- mapM freshVar txs
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
              mapM_ (\y -> addDecrTerm y []) ys
              GHC.mkLams ys <$$> synthesizeBasic CaseSplit " Function " goalType
      where (_, (xs, txs, _), to) = bkArrow t 

    go t = error (" Unmatched t = " ++ show t)

-- TODO: Decide whether it is @CaseSplit@ or @TermGen@.
data Mode 
  = CaseSplit -- ^ First case split and then generate terms.
  | TermGen   -- ^ First generate terms and then case split.
  deriving Eq

synthesizeBasic :: Mode -> String -> SpecType -> SM [CoreExpr]
synthesizeBasic m s t = do
  let ts = unifyWith (toType t) -- ^ All the types that are used for instantiation.
  if null ts  then  modify (\s -> s { sUGoalTy = Nothing } )
              else  modify (\s -> s { sUGoalTy = Just ts } )
  modify (\s -> s { sGoalTys = [] })
  fixEMem t
  -- if m == CaseSplit 
  --   then do senv <- getSEnv 
  --           es <- synthesizeMatch (" synthesizeMatch for t = " ++ show t ++ s) t
  --           if null es then synthesizeBasic TermGen "" t else return es
  --   else do 
  es <- genTerms s t
  if null es  then synthesizeMatch (" synthesizeMatch for t = " ++ show t ++ s) t
              else return es

synthesizeMatch :: String -> SpecType -> SM [CoreExpr]
synthesizeMatch s t = do
  scruts <- filterScrut
  id <- incrCase scruts
  if null scruts
    then return []
    else do let scrut = scruts !! id 
            trace (" CaseSplit " ++ show (map fst3 scruts) ++ 
                   " \n Scrutinee " ++ show (fst3 scrut)) $   
              withIncrDepth (matchOnExpr s t scrut)
            
filterScrut :: SM [(CoreExpr, Type, TyCon)]
filterScrut = do
  s <- get
  let em = sExprMem s
      xtop = sFix s
      foralls = (fst . sForalls) s
  let es0 = [((e, t, c), d) | ( t@(TyConApp c _), e, d ) <- em]
      es1 = filter (not . trivial . fst3 . fst) es0
      es2 = filter ((\e -> varOrApp e xtop foralls) . fst3 .fst) es1
      es3 = filter (not . isClassTyCon . thd3 . fst) es2
      es4 = filter (noPairLike . fst) es3
      es5 = sortOn snd es4
      es6 = map fst es5
  return es6

matchOnExpr :: String -> SpecType -> (CoreExpr, Type, TyCon) -> SM [CoreExpr]
matchOnExpr s t (GHC.Var v, tx, c) 
  = matchOn s t (v, tx, c)
matchOnExpr s t (e, tx, c)
  = do  freshV <- freshVarType tx
        freshSpecTy <- liftCG $ trueTy tx
        addEnv freshV freshSpecTy
        es <- matchOn s t (freshV, tx, c)
        return $ GHC.Let (GHC.NonRec freshV e) <$> es

matchOn :: String -> SpecType -> (Var, Type, TyCon) -> SM [CoreExpr]
matchOn s t (v, tx, c) =
  (GHC.Case (GHC.Var v) v tx <$$> sequence) <$> mapM (makeAlt s t (v, tx)) (tyConDataCons c)


makeAlt :: String -> SpecType -> (Var, Type) -> DataCon -> SM [GHC.CoreAlt]
makeAlt s t (x, TyConApp _ ts) c = locally $ do -- (AltCon, [b], Expr b)
  ts <- liftCG $ mapM trueTy τs
  xs <- mapM freshVar ts    
  addsEnv $ zip xs ts 
  addsEmem $ zip xs ts 
  addDecrTerm x xs
  liftCG0 (\γ -> caseEnv γ x mempty (GHC.DataAlt c) xs Nothing)
  es <- synthesizeBasic TermGen (s ++ " makeAlt for " ++ show c ++ " with vars " ++ show xs ++ " for t " ++ show t) t
  return $ (GHC.DataAlt c, xs, ) <$> es
  where 
    (_, _, τs) = dataConInstSig c ts
makeAlt s _ _ _ = error $ "makeAlt.bad argument " ++ s
