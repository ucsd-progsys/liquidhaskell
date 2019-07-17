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


notrace :: String -> a -> a 
notrace _ a = a 

-- containt GHC primitives
-- JP: Should we get this from REnv instead?
initSSEnv :: CGInfo -> SSEnv
initSSEnv info = M.fromList (filter iNeedIt (mkElem <$> prims))
  where
    mkElem (v, lt) = (F.symbol v, (val lt, v))
    prims = gsCtors $ gsData $ giSpec $ ghcI info
    iNeedIt (_, (_, v)) = v `elem` (dataConWorkId <$> [{- nilDataCon, -} consDataCon]) -- PB: I'm not sure that we need `[]`.



synthesize :: FilePath -> F.Config -> CGInfo -> IO [Error]
synthesize tgt fcfg cginfo = mapM goSCC $ holeDependencySSC $ holesMap cginfo -- TODO: foldM filled holes to dependencies. XXX
  where 
    goSCC (AcyclicSCC v) = go v
    goSCC (CyclicSCC []) = error "synthesize goSCC: unreachable"
    goSCC (CyclicSCC vs@((_, HoleInfo{..}):_)) = return $ ErrHoleCycle hloc $ map (symbol . fst) vs

    go (x, HoleInfo t loc env (cgi,cge)) = do 
      fills <- synthesize' tgt fcfg cgi cge env (initSSEnv cginfo) x t 
      return $ ErrHole loc (if length fills > 0 then text "\n Hole Fills: " <+> pprintMany fills else mempty)
                       mempty (symbol x) t 


synthesize' :: FilePath -> F.Config -> CGInfo -> CGEnv -> REnv -> SSEnv -> Var -> SpecType -> IO [CoreExpr]
synthesize' tgt fcfg cgi ctx renv senv x tx = evalSM (go tx) tgt fcfg cgi ctx renv senv
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
              return $ notracepp ("numeric with " ++ show r) [GHC.Var $ mkVar (Just smtVal) def def]


    go t = do ys <- mapM freshVar txs
              let su = F.mkSubst $ zip xs ((EVar . symbol) <$> ys) 
              mapM_ (uncurry addEnv) (zip ys ((subst su)<$> txs)) 
              addEnv x $ decrType x tx ys (zip xs txs)
              GHC.mkLams ys <$$> synthesizeBasic (subst su to) 
      where (_, (xs, txs, _), to) = bkArrow t 

    

synthesizeBasic :: SpecType -> SM [CoreExpr]
synthesizeBasic t = do
  es <- genTerms t
  filterElseM (hasType t) es $ do
    senv <- getSEnv
    lenv <- getLocalEnv 
    synthesizeMatch lenv senv t




-- Generate terms that have type t
genTerms :: SpecType -> SM [CoreExpr] 
genTerms specTy = 
  do  senv <- ssEnv <$> get
      let τ            = toType specTy
          cands        = findCandidates senv τ
          filterFunFun   (_, (ty, _)) = not $ isBasic ty
          funTyCands'  = filter filterFunFun cands
          funTyCands   = map (\(s, (ty, v)) -> (s, (instantiateType τ ty, v))) funTyCands'


          initEMem     = initExprMemory τ senv
      finalEMem <- withDepthFill maxAppDepth initEMem funTyCands
      let result       = takeExprs $ filter (\(t, _) -> t == τ) finalEMem 
      -- trace ("\n[ Expressions ] " ++ show result) $
      return result

maxAppDepth :: Int 
maxAppDepth = 6

-- PB: We need to combine that with genTerms and synthesizeBasic
withDepthFill :: Int -> ExprMemory -> [(Symbol, (Type, Var))] -> SM ExprMemory
withDepthFill depth exprMem funTyCands = do 
  exprMem' <- fillMany exprMem funTyCands exprMem
  if depth > 0 
    then withDepthFill (depth - 1) exprMem' funTyCands
    else return exprMem 

type ExprMemory = [(Type, CoreExpr)]
-- Initialized with basic type expressions
-- e.g. b  --- x_s3
--     [b] --- [], x_s0, x_s4
initExprMemory :: Type -> SSEnv -> ExprMemory
initExprMemory τ ssenv = 
  let senv    = M.toList ssenv 
      senv'   = filter (\(_, (t, _)) -> isBasic (toType t)) senv 
      senv''  = map (\(_, (t, v)) -> (toType t, GHC.Var v)) senv' 
      senv''' = map (\(t, e) -> (instantiateType τ t, e)) senv''
  in  senv'''


-- Produce new expressions from expressions currently in expression memory (ExprMemory).
-- Only candidate terms with function type (funTyCands) can be passed as second argument.
fillMany :: ExprMemory -> [(Symbol, (Type, Var))] -> ExprMemory -> SM ExprMemory 
fillMany _       []             accExprs = return accExprs
fillMany exprMem (cand : cands) accExprs = do
  let (_, (htype, _))   = cand
      subgoals'         = createSubgoals htype 
      resultTy          = last subgoals' 
      subgoals          = take (length subgoals' - 1) subgoals'
      argCands          = map (withSubgoal exprMem) subgoals 
      
  withType <- fillOne cand argCands
  let newExprs          = map (resultTy, ) withType
      accExprs'         = accExprs ++ newExprs
  fillMany exprMem cands accExprs'


-- PB: Currently, works with arity 1 or 2 (see below)...
-- Also, I don't think that it works for higher order e.g. map :: (a -> b) -> [a] -> [b].
-- Takes a function and a list of correct expressions for every argument
-- and returns a list of new expressions.
fillOne :: (Symbol, (Type, Var)) -> [[CoreExpr]] -> SM [CoreExpr]
fillOne funTyCand argCands = 
  let (_, (t, v)) = funTyCand
      arity       = length argCands 
      sg'         = createSubgoals t 
      -- resTy       = last sg
      sg          = take (length sg' - 1) sg'
  in  {- trace ("[ fillOne ] Function " ++ show v ++ " with subgoals = " ++ show (map showTy sg)) $ -} if arity == 1 
    -- GHC.App (GHC.Var v) v'
        then  do  idx <- incrSM -- id to generate new variable
                  return [ 
                    let letv' = mkVar (Just "x") idx (head sg)
                    in  case v' of 
                          GHC.Var _ -> GHC.App (GHC.Var v) v' 
                          _         -> GHC.Let (GHC.NonRec letv' v') (GHC.App (GHC.Var v) (GHC.Var letv')) | v' <- head argCands ]
        else  if arity == 2
                then do
                  !idx  <- incrSM  
                  !idx' <- incrSM 

                  return 
                    [ case v' of 
                        GHC.Var _ -> 
                          case v'' of 
                            GHC.Var _ -> GHC.App (GHC.App (GHC.App (GHC.Var v) (GHC.Type (head sg))) v') v'' 
                            _         -> 
                              let letv'' = mkVar (Just "x") idx' (sg !! 1)
                              in  GHC.Let (GHC.NonRec letv'' v'') (GHC.App (GHC.App (GHC.App (GHC.Var v) (GHC.Type (head sg)) ) v') (GHC.Var letv'')) 
                        _         -> 
                          let letv' = mkVar (Just "x") idx (head sg) 
                          in  GHC.Let (GHC.NonRec letv' v') (
                            case v'' of
                              GHC.Var _ -> 
                                GHC.App (GHC.App (GHC.Var v) (GHC.Var letv')) v''
                              _         -> 
                                let letv'' = mkVar (Just "x") idx' (sg !! 1) 
                                in  GHC.Let (GHC.NonRec letv'' v'') (GHC.App (GHC.App (GHC.Var v) (GHC.Var letv')) (GHC.Var letv'')))
                        | v'  <- head argCands, 
                          v'' <- argCands !! 1
                    ]
                else error $ "[ fillOne ] Function: " ++ show v


-- withSubgoal :: a type from subgoals 
-- Returns all expressions in ExprMemory that have the same type.
withSubgoal :: ExprMemory -> Type -> [CoreExpr]
withSubgoal []               _ = []
withSubgoal ((t, e) : exprs) τ = 
  if τ == t 
    then e : withSubgoal exprs τ
    else withSubgoal exprs τ


-- Removes forall from type and replaces
-- type variables from the first argument to the second argument.
-- Returns the new type.
instantiateType :: Type -> Type -> Type 
instantiateType τ t = 
  let t' = substInType t (varsInType τ)
  in  case t' of 
        GHC.ForAllTy _ t'' -> t''
        _                  -> t'  


-- Subgoals are function's arguments.
createSubgoals :: Type -> [Type] 
createSubgoals (GHC.ForAllTy _ htype) = createSubgoals htype
createSubgoals (GHC.FunTy t1 t2)      = t1 : createSubgoals t2
createSubgoals t                      = [t]



filterCands :: [(Symbol, (Type, Var))] -> Type -> [(Symbol, (Type, Var))]
filterCands []             _  = []
filterCands (cand : cands) ty = 
  let (_, (candType, _)) = cand
      isCand   = goalType ty candType
  in  if isCand
        then cand : filterCands cands ty
        else filterCands cands ty

findCandidates :: SSEnv -> Type -> [(Symbol, (Type, Var))]
findCandidates senv goalTy = 
  let senvLst   = M.toList senv
      senvLst'  = map (\(sym, (spect, var)) -> (sym, (toType spect, var))) senvLst
      -- filterFun (_, (specT, _)) = goalType goalTy specT
      -- candTerms = filter filterFun senvLst'
      candTerms = filterCands senvLst' goalTy 
  in  candTerms

-- Select all functions with result type equal with goalType
--        | goal |
goalType :: Type -> Type -> Bool
goalType τ t@(GHC.ForAllTy (TvBndr var _) htype) = 
  let substHType = substInType htype (varsInType τ)
  in  goalType τ substHType
goalType τ t@(GHC.FunTy _ t'') -- τ: base types
  | t'' == τ  = True
  | otherwise = goalType τ t''
goalType τ                 t 
  | τ == t    = True
  | otherwise = False

-- TODO: More than one type variables in type (what happens in forall case with that?).
-- use Language.Haskell.Liquid.GHC.TypeRep.subst instead 
substInType :: Type -> [TyVar] -> Type 
substInType t [tv] = substInType' tv t
  where 
    substInType' tv (GHC.TyVarTy var)                = GHC.TyVarTy tv
    substInType' tv (GHC.ForAllTy (TvBndr var x) ty) = GHC.ForAllTy (TvBndr tv x) (substInType' tv ty)
    substInType' tv (GHC.FunTy t0 t1)                = GHC.FunTy (substInType' tv t0) (substInType' tv t1)
    substInType' tv (GHC.AppTy t0 t1)                = GHC.AppTy (substInType' tv t0) (substInType' tv t1)
    substInType' tv (GHC.TyConApp c ts)              = GHC.TyConApp c (map (substInType' tv) ts)
    substInType' _  t                                = error $ "[substInType'] Shouldn't reach that point for now " ++ showTy t
substInType _ vars = error $ "My example has one type variable. Vars: " ++ show (map symbol vars)

-- Find all variables in type
varsInType :: Type -> [TyVar] 
varsInType t = (map head . group . sort) (varsInType' t)
  where
    varsInType' (GHC.TyVarTy var)                = [var]
    varsInType' (GHC.ForAllTy (TvBndr var _) ty) = var : varsInType' ty
    varsInType' (GHC.FunTy t0 t1)                = varsInType' t0 ++ varsInType' t1
    varsInType' (GHC.AppTy t0 t1)                = varsInType' t0 ++ varsInType' t1 
    varsInType' (GHC.TyConApp c ts)              = foldr (\x y -> concat (map varsInType' ts) ++ y) [] ts
    varsInType' t                                = error $ "[varsInType] Shouldn't reach that point for now " ++ showTy t



-- Panagiotis TODO: here I only explore the first one                     
--  We need the most recent one
synthesizeMatch :: LEnv -> SSEnv -> SpecType -> SM [CoreExpr]
synthesizeMatch lenv γ t 
  -- | [] <- es 
  -- = return def

  -- | otherwise 
  -- = maybe def id <$> monadicFirst 
  = notrace ("[synthesizeMatch] es = " ++ show es) $ 
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
  liftCG0 (\γ -> caseEnv γ x mempty (GHC.DataAlt c) xs Nothing)
  es <- synthesizeBasic t
  return $ (\e -> (GHC.DataAlt c, xs, e)) <$> es
  where 
    (_, _, τs) = dataConInstSig c (toType <$> ts)
makeAlt _ _ _ _ = error "makeAlt.bad argument"
    

hasType :: SpecType -> CoreExpr -> SM Bool
hasType t !e = do 
  x  <- freshVar t 
  st <- get 
  r <- liftIO $ check (sCGI st) (sCGEnv st) (sFCfg st) x e t 
  liftIO $ putStrLn ("Checked:  Expr = " ++ showPpr e ++ " of type " ++ show t ++ "\n Res = " ++ show r)
  return r 






symbolExpr :: GHC.Type -> Symbol -> SM CoreExpr 
symbolExpr τ x = incrSM >>= (\i -> return $ notracepp ("symExpr for " ++ showpp x) $  GHC.Var $ mkVar (Just $ symbolString x) i τ)




