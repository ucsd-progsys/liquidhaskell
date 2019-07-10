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
import           Language.Haskell.Liquid.Constraint.Fresh (trueTy)
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Types hiding (SEnv, SVar, Error)
import qualified Language.Fixpoint.Types        as F 
import qualified Language.Fixpoint.Types.Config as F


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
import qualified Data.Map as Map 
import           Data.List.Extra


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
              mapM (uncurry addEnv) (zip ys ((subst su)<$> txs)) 
              addEnv x $ decrType x tx ys (zip xs txs)
              GHC.mkLams ys <$$> synthesizeBasic (subst su to) 
      where (_, (xs, txs, _), to) = bkArrow t 

    
-- synthesizeBasic :: SpecType -> SM [CoreExpr]
-- synthesizeBasic t = do 
--   rtc_cands <- genTerms t 
--   trace ("[ synthesizeBasic ]" ++ show rtc_cands) $
--     do  es <- generateETerms t
--         filterElseM (hasType t) es $ do
--             apps <- generateApps t
--             filterElseM (hasType t) apps $ do
--               senv <- getSEnv
--               lenv <- getLocalEnv
--               synthesizeMatch lenv senv t

{- 
-- James: sketch out app some
generateApps :: SpecType -> SM [CoreExpr]
generateApps t = do
  env <- M.toList . ssEnv <$> get

  fs <- concat <$> mapM generateF env

  error "TODO"

synthesizeBasic :: SpecType -> SM [CoreExpr]
synthesizeBasic t = do es <- generateETerms t
                       filterElseM (hasType t) es $ do
                          apps <- generateApps t
                          filterElseM (hasType t) apps $ do
                            senv <- getSEnv
                            lenv <- getLocalEnv
                            notrace ("apps = " ++ show apps) $ 
                              synthesizeMatch lenv senv t -- JP: Should we remove this from `synthesizeBasic`? Filter result?
                       


  where
    generateF :: (Symbol, (SpecType, Var)) -> SM [(SpecType, CoreExpr)]
    generateF (_, (t, v)) = do
        let t' = RFun _freshSymbol (RVar _var _reft) t _reft'  -- JP: What's the right constructor here???
        es <- synthesizeBasic t'

        -- Generate arg here?
        error "TODO"

    _freshSymbol = undefined
    _var = undefined
    _reft = undefined
    _reft' = undefined
-}

    -- PB: Possibly replace with this synthesizeBasic.
    -- There is a bug for now with hasType and some expressions,
    -- e.g. hasType t (stutter (stutter x_s0)).

synthesizeBasic :: SpecType -> SM [CoreExpr]
synthesizeBasic t = do
  es <- genTerms t
  filterElseM (hasType t) es $ do
    senv <- getSEnv
    lenv <- getLocalEnv 
    synthesizeMatch lenv senv t


isBasic :: Type -> Bool
isBasic TyConApp{}     = True
isBasic TyVarTy {}     = True
isBasic (ForAllTy _ t) = isBasic t
isBasic AppTy {}       = False 
isBasic LitTy {}       = False
isBasic _              = False


-- PB: This is to replace generateETerms and generateApps.
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
      let result       = takeExprs finalEMem 
      trace ("\n[ Expressions ] " ++ show result) (return result) 

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
      resultTy          = last subgoals 
      subgoals          = take (length subgoals' - 1) subgoals'
      argCands          = map (withSubgoal exprMem) subgoals 
      
  withType <- fillOne cand argCands
  let newExprs          = map (resultTy, ) withType
      accExprs'         = accExprs ++ newExprs
  fillMany exprMem cands accExprs'


-- Let  (Language.Haskell.Liquid.GHC.API.Bind b)
--      (Language.Haskell.Liquid.GHC.API.Expr b)
-- PB: Currently, works with arity 1 or 2 (see below)...
-- Also, I don't think that it works for higher order e.g. map :: (a -> b) -> [a] -> [b].
-- Takes a function and a list of correct expressions for every argument
-- and returns a list of new expressions.
fillOne :: (Symbol, (Type, Var)) -> [[CoreExpr]] -> SM [CoreExpr]
fillOne funTyCand argCands = 
  let (_, (t, v)) = funTyCand
      arity       = length argCands 
  in  if arity == 1 
    -- GHC.App (GHC.Var v) v'
        then  do  idx <- ssIdx <$> get -- id to generate new variable
                  let letv' = mkVar (Just "x") idx t
                  incrSM 
                  return [ 
                    case v' of 
                      GHC.Var _ -> GHC.App (GHC.Var v) v' 
                      _         -> GHC.Let (GHC.NonRec letv' v') (GHC.App (GHC.Var v) (GHC.Var letv')) | v' <- head argCands ]
        else  if arity == 2
                then do
                  idx <- ssIdx <$> get -- id to generate new variable
                  let letv' = mkVar (Just "x") idx t
                  incrSM 
                  idx' <- ssIdx <$> get
                  let letv'' = mkVar (Just "x") idx' t
                  incrSM
                  return 
                        [ case v' of 
                            GHC.Var _ -> GHC.App (GHC.App (GHC.Var v) v') v'' 
                            _         -> 
                              GHC.Let (GHC.NonRec letv' v') (
                                case v'' of 
                                  GHC.Var _ -> GHC.App (GHC.App (GHC.Var v) (GHC.Var letv')) v''
                                  _         -> GHC.Let (GHC.NonRec letv'' v'') (GHC.App (GHC.App (GHC.Var v) (GHC.Var letv')) (GHC.Var letv'')))
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




{- 
-- e-terms: var, constructors, function applications

-- This should generates all e-terms.
-- Now it generates variables and function applications in the environment.
-- TODO: Add constructors in the environment.
-- Note: Probably `generateApps` works for constructors as well.
generateETerms :: SpecType -> SM [CoreExpr] 
generateETerms t = do 
  lenv <- M.toList . ssEnv <$> get 
  let delimiterStr = "\n************************************\n"
  notrace (delimiterStr ++ "[generateETerms] lenv = " ++ show lenv ++ " " ++ delimiterStr) $ 
    return [ GHC.Var v | (x, (tx, v)) <- lenv, τ == toType tx ] 
  where τ = toType t 

generateApps :: SpecType -> SM [CoreExpr]
generateApps t = do
  env <- M.toList . ssEnv <$> get

  fs <- concat <$> mapM generateF env

  error "TODO"


  where
    generateF :: (Symbol, (SpecType, Var)) -> SM [(SpecType, CoreExpr)]
    generateF (_, (t, v)) = do
        let t' = RFun _freshSymbol (RVar _var _reft) t _reft'  -- JP: What's the right constructor here???
        es <- synthesizeBasic t'

        -- Generate arg here?
        error "TODO"

    _freshSymbol = undefined
    _var = undefined
    _reft = undefined
    _reft' = undefined

--   lenv <- M.toList . ssEnv <$> get
--   decrTerms <- ssDecrTerm <$> get
--   let τ = toType t
--   case generateApps' decrTerms lenv lenv τ of
--     [] -> return []
--     l  -> return l

generateApps' :: SSDecrTerm -> [(Symbol, (SpecType, Var))] -> [(Symbol, (SpecType, Var))] -> GHC.Type -> [CoreExpr]
generateApps' _         []      _  _ = []
generateApps' decrTerms (h : t) l2 τ = generateApps'' decrTerms h l2 τ ++ generateApps' decrTerms t l2 τ

generateApps'' :: SSDecrTerm -> (Symbol, (SpecType, Var)) -> [(Symbol, (SpecType, Var))] -> GHC.Type -> [CoreExpr]
generateApps'' _         _                 []                       _ = []
generateApps'' decrTerms h@(_, (rtype, v)) ((_, (rtype', v')) : es) τ = 
  let htype  = toType rtype
      htype' = toType rtype'
      t  = typeAppl htype  htype'
      t' = typeAppl htype' htype
  in  
  -- in  trace ( "\n ***** t = "   ++ 
  --             showTy t ++ "\n"  ++ 
  --             "       var = "   ++ 
  --             show v ++ "\n"    ++
  --             "\n ***** t' = "  ++ 
  --             showTy t' ++ "\n" ++ 
  --             "       var = "   ++ 
  --             show v' ++ "\n"   ++
  --             "\n ***** τ = "   ++ 
  --             showTy τ ++ "\n"    ) $ 
      case t of
        Nothing ->
          case t' of 
            Nothing -> generateApps'' decrTerms h es τ 
            Just _  -> 
              case lookup v decrTerms of
                Nothing   -> GHC.App (GHC.Var v') (GHC.Var v) : generateApps'' decrTerms h es τ
                Just vars -> generateApps'' decrTerms h es τ
        Just _  -> 
          case lookup v' decrTerms of
            Nothing   -> GHC.App (GHC.Var v) (GHC.Var v') : generateApps'' decrTerms h es τ
            Just vars -> generateApps'' decrTerms h es τ

typeAppl :: Type -> Type -> Maybe Type
typeAppl (GHC.FunTy t' t'') t''' 
  | t'' == t''' = Just t'
typeAppl _                  _   = Nothing 
-}


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

maxDepth :: Int 
maxDepth = 1 

matchOn :: SpecType -> (Var, SpecType, TyCon) -> SM [CoreExpr]
matchOn t (v, tx, c) = (GHC.Case (GHC.Var v) v (toType tx) <$$> sequence) <$> mapM (makeAlt scrut t (v, tx)) (tyConDataCons c)
  where scrut = v
  -- JP: Does this need to be a foldM? Previous pattern matches could influence expressions of later patterns?

(<$$>) :: (Functor m, Functor n) => (a -> b) -> m (n a) -> m (n b)
(<$$>) = fmap . fmap

makeAlt :: Var -> SpecType -> (Var, SpecType) -> DataCon -> SM [GHC.CoreAlt]
makeAlt var t (x, tx@(RApp _ ts _ _)) c = locally $ do -- (AltCon, [b], Expr b)
  ts <- liftCG $ mapM trueTy τs
  xs <- mapM freshVar ts    
  addsEnv $ zip xs ts 
  -- begin: TOXIC
  env <- ssEnv <$> get
  let htVar = toType $ fst $ fromJust $ M.lookup (symbol var) env
      xs' = filter (\χ -> htVar == (case M.lookup (symbol χ) env of { Nothing -> error $ "xs = " ++ show xs; Just xs'' -> toType $ fst xs'' } )) xs 
  addDecrTerm var xs'
  -- end: TOXIC
  liftCG0 (\γ -> caseEnv γ x mempty (GHC.DataAlt c) xs Nothing)
  es <- synthesizeBasic t
  return $ (\e -> (GHC.DataAlt c, xs, e)) <$> es
  where 
    (_, _, τs) = dataConInstSig c (toType <$> ts)
makeAlt _ _ _ _ = error "makeAlt.bad argument"
    

hasType :: SpecType -> CoreExpr -> SM Bool
hasType t e = trace ("[ Entered: hasType ] with expr = " ++ show e) $ do 
  x  <- freshVar t 
  st <- get 
  r <- liftIO $ check (sCGI st) (sCGEnv st) (sFCfg st) x e t 
  liftIO $ putStrLn ("Checked:  Expr = " ++ showPpr e ++ " of type " ++ show t ++ "\n Res = " ++ show r)
  return r 

filterElseM :: Monad m => (a -> m Bool) -> [a] -> m [a] -> m [a]
filterElseM f as ms = do
    rs <- filterM f as
    if null rs then
        ms
    else
        return rs

-- findM :: Monad m => (a -> m Bool) -> [a] -> m (Maybe a)
-- findM _ []     = return Nothing
-- findM p (x:xs) = do b <- p x ; if b then return (Just x) else findM p xs 

{- 
    {- OLD STUFF -}
    -- Type Variable
    go (RVar α _)        = (`synthesizeRVar` α) <$> getSEnv
    -- Function 

    -- Data Type, e.g., c = Int and ts = [] or c = List and ts = [a] 
              -- return def
    go (RApp _c _ts _ _) 
      = return def 
    -- Type Application, e.g, m a 
    go RAppTy{} = return def 


    -- Fancy Liquid Types to be ignored for now since they do not map to haskell types
    go (RImpF _ _ t _) = go t 
    go (RAllP _ t)     = go t 
    go (RAllS _ t)     = go t 
    go (RAllE _ _ t)   = go t 
    go (REx _ _ t)     = go t 
    go (RRTy _ _ _ t)  = go t 
    go (RExprArg _)    = return def 
    go (RHole _)       = return def 
-}


symbolExpr :: GHC.Type -> Symbol -> SM CoreExpr 
symbolExpr τ x = incrSM >>= (\i -> return $ notracepp ("symExpr for " ++ showpp x) $  GHC.Var $ mkVar (Just $ symbolString x) i τ)

-------------------------------------------------------------------------------
-- | Synthesis Monad ----------------------------------------------------------
-------------------------------------------------------------------------------

-- The state keeps a unique index for generation of fresh variables 
-- and the environment of variables to types that is expanded on lambda terms
type SSEnv = M.HashMap Symbol (SpecType, Var)
type SSDecrTerm = [(Var, [Var])]
data SState 
  = SState { rEnv       :: REnv -- Local Binders Generated during Synthesis 
           , ssEnv      :: SSEnv -- Local Binders Generated during Synthesis 
           , ssIdx      :: Int
           , ssDecrTerm :: SSDecrTerm 
           , sContext   :: SMT.Context
           , sCGI       :: CGInfo
           , sCGEnv     :: CGEnv
           , sFCfg      :: F.Config
           , sDepth     :: Int 
           }
type SM = StateT SState IO
 
locally :: SM a -> SM a 
locally act = do 
  st <- get 
  r <- act 
  modify $ \s -> s{sCGEnv = sCGEnv st, sCGI = sCGI st}
  return r 


evalSM :: SM a -> FilePath -> F.Config -> CGInfo -> CGEnv -> REnv -> SSEnv -> IO a 
evalSM act tgt fcfg cgi cgenv renv env = do 
  ctx <- SMT.makeContext fcfg tgt  
  r <- evalStateT act (SState renv env 0 [] ctx cgi cgenv fcfg 0)
  SMT.cleanupContext ctx 
  return r 

getSEnv :: SM SSEnv
getSEnv = ssEnv <$> get 

type LEnv = M.HashMap Symbol SpecType -- | Local env.

getLocalEnv :: SM LEnv
getLocalEnv = (reLocal . rEnv) <$> get

getSDecrTerms :: SM SSDecrTerm 
getSDecrTerms = ssDecrTerm <$> get

addsEnv :: [(Var, SpecType)] -> SM () 
addsEnv xts = 
  mapM_ (\(x,t) -> modify (\s -> s {ssEnv = M.insert (symbol x) (t,x) (ssEnv s)})) xts  


addEnv :: Var -> SpecType -> SM ()
addEnv x t = do 
  liftCG0 (\γ -> γ += ("arg", symbol x, t))
  modify (\s -> s {ssEnv = M.insert (symbol x) (t,x) (ssEnv s)}) 

addDecrTerm :: Var -> [Var] -> SM ()
addDecrTerm x vars = do
  decrTerms <- getSDecrTerms 
  case lookup x decrTerms of 
    Nothing    -> modify (\s -> s { ssDecrTerm = (x, vars) : (ssDecrTerm s) } )
    Just vars' -> do
      let ix = elemIndex (x, vars') decrTerms
      case ix of 
        Nothing  -> error $ "[addDecrTerm] It should have been there " ++ show x 
        Just ix' -> 
          let (left, right) = splitAt ix' decrTerms 
          in  modify (\s -> s { ssDecrTerm =  left ++ [(x, vars ++ vars')] ++ right } )


liftCG0 :: (CGEnv -> CG CGEnv) -> SM () 
liftCG0 act = do 
  st <- get 
  let (cgenv, cgi) = runState (act (sCGEnv st)) (sCGI st) 
  modify (\s -> s {sCGI = cgi, sCGEnv = cgenv}) 



liftCG :: CG a -> SM a 
liftCG act = do 
  st <- get 
  let (x, cgi) = runState act (sCGI st) 
  modify (\s -> s {sCGI = cgi})
  return x 


freshVar :: SpecType -> SM Var
freshVar t = (\i -> mkVar (Just "x") i (toType t)) <$> incrSM

withIncrDepth :: Monoid a => SM a -> SM a
withIncrDepth m = do 
    s <- get 
    let d = sDepth s

    if d + 1 > maxDepth then
        return mempty

    else do
        put s{sDepth = d + 1}

        r <- m

        modify $ \s -> s{sDepth = d}

        return r


incrSM :: SM Int 
incrSM = do s <- get 
            put s{ssIdx = ssIdx s + 1}
            return (ssIdx s)

-- The rest will be added when needed.
-- Replaces    | old w   | new  | symbol name in expr.
substInFExpr :: Symbol -> Symbol -> Expr -> Expr
substInFExpr pn nn e = subst1 e (pn, EVar nn)

-------------------------------------------------------------------------------
-- | Misc ---------------------------------------------------------------------
-------------------------------------------------------------------------------

solDelim :: String
solDelim = "\n*********************************************\n"

pprintMany :: (PPrint a) => [a] -> Doc
pprintMany xs = vcat [ F.pprint x $+$ text solDelim | x <- xs ]

showGoals :: [[String]] -> String
showGoals []             = ""
showGoals (goal : goals) = 
  show goal        ++ 
  "\n"             ++ 
  replicate 12 ' ' ++ 
  showGoals goals

takeExprs = map snd 
-------------------------------------------------------------------------------
-- | To be removed ------------------------------------------------------------
-------------------------------------------------------------------------------

-- To be removed
generateApps :: SpecType -> SM [CoreExpr]
generateApps t = do
  lenv <- M.toList . ssEnv <$> get
  decrTerms <- ssDecrTerm <$> get
  let τ = toType t
  case generateApps' decrTerms lenv lenv τ of
    [] -> return []
    l  -> return l


-- To be removed
generateApps' :: SSDecrTerm -> [(Symbol, (SpecType, Var))] -> [(Symbol, (SpecType, Var))] -> GHC.Type -> [CoreExpr]
generateApps' _         []      _  _ = []
generateApps' decrTerms (h : t) l2 τ = 
  generateApps'' decrTerms h l2 τ ++ generateApps' decrTerms t l2 τ

-- To be removed
generateApps'' :: SSDecrTerm -> (Symbol, (SpecType, Var)) -> [(Symbol, (SpecType, Var))] -> GHC.Type -> [CoreExpr]
generateApps'' _         _                 []                       _ = []
generateApps'' decrTerms h@(_, (rtype, v)) ((_, (rtype', v')) : es) τ = 
  let htype  = toType rtype
      htype' = toType rtype'
      t  = typeAppl htype  htype'
      t' = typeAppl htype' htype
  in  case t of
        Nothing ->
          case t' of 
            Nothing -> generateApps'' decrTerms h es τ 
            Just _  -> 
              case lookup v decrTerms of
                Nothing   -> GHC.App (GHC.Var v') (GHC.Var v) : generateApps'' decrTerms h es τ
                Just vars -> generateApps'' decrTerms h es τ
        Just _  -> 
          case lookup v' decrTerms of
            Nothing   -> GHC.App (GHC.Var v) (GHC.Var v') : generateApps'' decrTerms h es τ
            Just vars -> generateApps'' decrTerms h es τ

-- To be removed
typeAppl :: Type -> Type -> Maybe Type
typeAppl (GHC.FunTy t' t'') t''' 
  | t' == t''' = Just t'
typeAppl _                  _   = Nothing 


-- This should generates all e-terms.
-- Now it generates variables and function applications in the environment.
-- TODO: Add constructors in the environment.
-- Note: Probably `generateApps` works for constructors as well.
-- To be removed
generateETerms :: SpecType -> SM [CoreExpr] 
generateETerms t = do 
  lenv <- M.toList . ssEnv <$> get 
  return [ GHC.Var v | (x, (tx, v)) <- lenv, τ == toType tx ] 
  where τ = toType t 

