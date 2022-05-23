{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Haskell.Liquid.Synthesize.Monad where


import           Language.Haskell.Liquid.GHC.API as GHC
import           Language.Haskell.Liquid.Bare.Resolve
                                               as B
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Synthesize.GHC
                                         hiding ( SSEnv )
import           Language.Haskell.Liquid.Synthesize.Misc
                                         hiding ( notrace )
import qualified Language.Fixpoint.Smt.Interface
                                               as SMT
import           Language.Fixpoint.Types hiding ( SEnv
                                                , SVar
                                                , Error
                                                )
import qualified Language.Fixpoint.Types       as F
import qualified Language.Fixpoint.Types.Config
                                               as F
import           Control.Monad.State.Lazy
import qualified Data.HashMap.Strict           as M
import           Data.Maybe
import           Data.List
import           Data.Tuple.Extra

localMaxMatchDepth :: SM Int 
localMaxMatchDepth = maxMatchDepth . getConfig . sCGEnv <$> get

-------------------------------------------------------------------------------
-- | Synthesis Monad ----------------------------------------------------------
-------------------------------------------------------------------------------

-- The state keeps a unique index for generation of fresh variables 
-- and the environment of variables to types that is expanded on lambda terms
type SSEnv = M.HashMap Symbol (SpecType, Var)
type SSDecrTerm = [(Var, [Var])]

type ExprMemory = [(Type, CoreExpr, Int)]
type T = M.HashMap Type (CoreExpr, Int)
data SState 
  = SState { rEnv       :: !REnv 
           , ssEnv      :: !SSEnv -- Local Binders Generated during Synthesis 
           , ssIdx      :: !Int
           , ssDecrTerm :: !SSDecrTerm 
           , sContext   :: !SMT.Context
           , sCGI       :: !CGInfo
           , sCGEnv     :: !CGEnv
           , sFCfg      :: !F.Config
           , sDepth     :: !Int
           , sExprMem   :: !ExprMemory 
           , sExprId    :: !Int
           , sArgsId    :: !Int
           , sArgsDepth :: !Int
           , sUniVars   :: ![Var]
           , sFix       :: !Var
           , sGoalTys   :: ![Type]
           , sGoalTyVar :: !(Maybe [TyVar])
           , sUGoalTy   :: !(Maybe [Type])     -- Types used for instantiation.
                                               --   Produced by @withUnify@.
           , sForalls   :: !([Var], [[Type]])  -- [Var] are the parametric functions (except for the fixpoint)
                                               --    e.g. Constructors, top-level functions.
                                               -- [[Type]]: all the types that have instantiated [Var] so far.
           , caseIdx    :: !Int                -- [ Temporary ] Index in list of scrutinees.
           , scrutinees :: ![(CoreExpr, Type, TyCon)]
           }

type SM = StateT SState IO

localMaxAppDepth :: SM Int 
localMaxAppDepth = maxAppDepth . getConfig . sCGEnv <$> get

localMaxArgsDepth :: SM Int
localMaxArgsDepth = maxArgsDepth . getConfig . sCGEnv <$> get

locally :: SM a -> SM a 
locally act = do 
  st <- get 
  r <- act 
  modify $ \s -> s{sCGEnv = sCGEnv st, sCGI = sCGI st, sExprMem = sExprMem st, scrutinees = scrutinees st}
  return r 


evalSM :: SM a -> SMT.Context -> SSEnv -> SState -> IO a 
evalSM act ctx env st = do 
  let st' = st {ssEnv = env}
  r <- evalStateT act st'
  _ <- SMT.cleanupContext ctx 
  return r 

initState :: SMT.Context -> F.Config -> CGInfo -> CGEnv -> REnv -> Var -> [Var] -> SSEnv -> IO SState 
initState ctx fcfg cgi cgenv renv xtop uniVars env = 
  return $ SState renv env 0 [] ctx cgi cgenv fcfg 0 exprMem0 0 0 0 uniVars xtop [] Nothing Nothing ([], []) 0 []
  where exprMem0 = initExprMem env

getSEnv :: SM SSEnv
getSEnv = ssEnv <$> get 

getSEMem :: SM ExprMemory
getSEMem = sExprMem <$> get

getSFix :: SM Var 
getSFix = sFix <$> get

getSUniVars :: SM [Var]
getSUniVars = sUniVars <$> get

getSDecrTerms :: SM SSDecrTerm 
getSDecrTerms = ssDecrTerm <$> get

addsEnv :: [(Var, SpecType)] -> SM () 
addsEnv xts = 
  mapM_ (\(x,t) -> modify (\s -> s {ssEnv = M.insert (symbol x) (t,x) (ssEnv s)})) xts  

addsEmem :: [(Var, SpecType)] -> SM () 
addsEmem xts = do 
  curAppDepth <- sExprId <$> get
  mapM_ (\(x,t) -> modify (\s -> s {sExprMem = (toType False t, GHC.Var x, curAppDepth+1) : (sExprMem s)})) xts  
  

addEnv :: Var -> SpecType -> SM ()
addEnv x t = do 
  liftCG0 (\γ -> γ += ("arg", symbol x, t))
  modify (\s -> s {ssEnv = M.insert (symbol x) (t,x) (ssEnv s)}) 

addEmem :: Var -> SpecType -> SM ()
addEmem x t = do 
  let ht0 = toType False t
  curAppDepth <- sExprId <$> get
  xtop <- getSFix 
  (ht1, _) <- instantiateTL
  let ht = if x == xtop then ht1 else ht0
  modify (\s -> s {sExprMem = (ht, GHC.Var x, curAppDepth) : sExprMem s})

---------------------------------------------------------------------------------------------
--                         Handle structural termination checking                          --
---------------------------------------------------------------------------------------------
addDecrTerm :: Var -> [Var] -> SM ()
addDecrTerm x vars = do
  decrTerms <- getSDecrTerms 
  case lookup x decrTerms of 
    Nothing    -> lookupAll x vars decrTerms
    Just vars' -> do
      let ix = elemIndex (x, vars') decrTerms
          newDecrs = thisReplace (fromMaybe (error " [ addDecrTerm ] Index ") ix) (x, vars ++ vars') decrTerms
      modify (\s -> s { ssDecrTerm =  newDecrs })

-- 
lookupAll :: Var -> [Var] -> SSDecrTerm -> SM ()
lookupAll x vars []               = modify (\s -> s {ssDecrTerm = (x, vars) : ssDecrTerm s})
lookupAll x vars ((xl, vs):decrs) =
  case find (== x) vs of
    Nothing -> lookupAll x vars decrs
    Just _  -> do
      sDecrs <- ssDecrTerm <$> get
      let newDecr  = (xl, vars ++ [x] ++ vs)
          i        = fromMaybe (error " Write sth ") (elemIndex (xl, vs) sDecrs)
          newDecrs = thisReplace i newDecr decrs
      modify (\s -> s { ssDecrTerm = newDecrs })

thisReplace :: Int -> a -> [a] -> [a]
thisReplace i x l
  = left ++ [x] ++ right
    where left  = take (i-1) l
          right = drop i l

-- | Entry point.
structuralCheck :: [CoreExpr] -> SM [CoreExpr]
structuralCheck es 
  = do  decr <- ssDecrTerm <$> get
        fix' <- sFix <$> get
        return (filter (notStructural decr fix') es)

structCheck :: Var -> CoreExpr -> (Maybe Var, [CoreExpr])
structCheck xtop var@(GHC.Var v)
  = if v == xtop 
      then (Just xtop, [])
      else (Nothing, [var])
structCheck xtop (GHC.App e1 (GHC.Type _))
  = structCheck xtop e1
structCheck xtop (GHC.App e1 e2)
  =  (mbVar, e2:es)
    where (mbVar, es) = structCheck xtop e1
structCheck xtop (GHC.Let _ e) 
  = structCheck xtop e
structCheck _ e 
  = error (" StructCheck " ++ show e)

notStructural :: SSDecrTerm -> Var -> CoreExpr -> Bool
notStructural decr xtop e
  = case v of
      Nothing -> True
      Just _  -> foldr (\x b -> isDecreasing' x decr || b) False args
  where (v, args) = structCheck xtop e

isDecreasing' :: CoreExpr -> SSDecrTerm -> Bool
isDecreasing' (GHC.Var v) decr
  = v `notElem` map fst decr
isDecreasing' _e _decr
  = True
---------------------------------------------------------------------------------------------
--                               END OF STRUCTURAL CHECK                                   --
---------------------------------------------------------------------------------------------

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


freshVarType :: Type -> SM Var
freshVarType t = (\i -> mkVar (Just "x") i t) <$> incrSM


freshVar :: SpecType -> SM Var
freshVar = freshVarType . toType False

withIncrDepth :: Monoid a => SM a -> SM a
withIncrDepth m = do 
    s <- get
    matchBound <- localMaxMatchDepth 
    let d = sDepth s
    if d + 1 > matchBound
      then return mempty
      else do put s{sDepth = d + 1}
              r <- m
              modify $ \t -> t{sDepth = d}
              return r
        
  
incrSM :: SM Int 
incrSM = do s <- get 
            put s{ssIdx = ssIdx s + 1}
            return (ssIdx s)

incrCase :: SM Int 
incrCase
  = do  s <- get 
        put s { caseIdx = caseIdx s + 1 }
        return (caseIdx s)
  
safeIxScruts :: Int -> [a] -> Maybe Int
safeIxScruts i l 
  | i >= length l = Nothing
  | otherwise     = Just i

symbolExpr :: Type -> F.Symbol -> SM CoreExpr 
symbolExpr τ x = incrSM >>= (\i -> return $ F.notracepp ("symExpr for " ++ F.showpp x) $  GHC.Var $ mkVar (Just $ F.symbolString x) i τ)


-------------------------------------------------------------------------------------------------------
----------------------------------------- Handle ExprMemory -------------------------------------------
-------------------------------------------------------------------------------------------------------

-- | Initializes @ExprMemory@ structure.
--    1. Transforms refinement types to conventional (Haskell) types.
--    2. All @Depth@s are initialized to 0.
initExprMem :: SSEnv -> ExprMemory
initExprMem sEnv = map (\(_, (t, v)) -> (toType False t, GHC.Var v, 0)) (M.toList sEnv)


-------------- Init @ExprMemory@ with instantiated functions with the right type (sUGoalTy) -----------
insEMem0 :: SSEnv -> SM ExprMemory
insEMem0 ssenv = do
  xtop      <- getSFix
  (ttop, _) <- instantiateTL
  mbUTy     <- sUGoalTy <$> get 
  uniVs <- sUniVars <$> get

  let ts = fromMaybe [] mbUTy
  ts0 <- snd . sForalls <$> get
  fs0 <- fst . sForalls <$> get
  modify ( \s -> s { sForalls = (fs0, ts : ts0) } )

  let handleIt e = case e of  GHC.Var v -> if xtop == v 
                                              then (instantiate e (Just uniVs), ttop) 
                                              else change e
                              _         -> change e
      change e =  let { e' = instantiateTy e mbUTy; t' = exprType e' } 
                  in  (e', t')

      em0 = initExprMem ssenv
  return $ map (\(_, e, i) -> let (e', t') = handleIt e
                              in  (t', e', i)) em0

instantiateTy :: CoreExpr -> Maybe [Type] -> CoreExpr
instantiateTy e mbTy = 
  case mbTy of 
    Nothing  -> e
    Just tys -> case applyTy tys e of 
                  Nothing -> e
                  Just e0 -> e0

-- | Used for instantiation: Applies types to an expression.
--   > The result does not have @forall@.
--   Nothing as a result suggests that there are more types than foralls in the expression.
applyTy :: [Type] -> GHC.CoreExpr -> Maybe GHC.CoreExpr
applyTy []     e =  case exprType e of 
                      ForAllTy{} -> Nothing
                      _          -> Just e
applyTy (t:ts) e =  case exprType e of
                      ForAllTy{} -> applyTy ts (GHC.App e (GHC.Type t))
                      _          -> Nothing

-- | Instantiation based on current goal-type.
fixEMem :: SpecType -> SM ()
fixEMem t
  = do  (fs, ts) <- sForalls <$> get
        let uTys = unifyWith (toType False t)
        needsFix <- case find (== uTys) ts of 
                      Nothing -> return True   -- not yet instantiated
                      Just _  -> return False  -- already instantiated

        when needsFix $
          do  modify (\s -> s { sForalls = (fs, uTys : ts)})
              let notForall e = case exprType e of {ForAllTy{} -> False; _ -> True}
                  es = map (\v -> instantiateTy (GHC.Var v) (Just uTys)) fs
                  fixEs = filter notForall es
              thisDepth <- sDepth <$> get
              let fixedEMem = map (\e -> (exprType e, e, thisDepth + 1)) fixEs
              modify (\s -> s {sExprMem = fixedEMem ++ sExprMem s})

------------------------------------------------------------------------------------------------
------------------------------ Special handle for the current fixpoint -------------------------
------------------------------------------------------------------------------------------------

-- | Instantiate the top-level variable.
instantiateTL :: SM (Type, GHC.CoreExpr)
instantiateTL = do
  uniVars <- getSUniVars 
  xtop <- getSFix
  let e = fromJust $ apply uniVars (GHC.Var xtop)
  return (exprType e, e)

-- | Applies type variables (1st argument) to an expression.
--   The expression is guaranteed to have the same level of 
--   parametricity (same number of @forall@) as the length of the 1st argument.
--   > The result has zero @forall@.
apply :: [Var] -> GHC.CoreExpr -> Maybe GHC.CoreExpr
apply []     e = 
  case exprType e of 
    ForAllTy {} -> Nothing
    _           -> Just e
apply (v:vs) e 
  = case exprType e of 
      ForAllTy{} -> apply vs (GHC.App e (GHC.Type (TyVarTy v)))
      _          -> Nothing

instantiate :: CoreExpr -> Maybe [Var] -> CoreExpr
instantiate e mbt = 
  case mbt of
    Nothing     -> e
    Just tyVars -> case apply tyVars e of 
                      Nothing -> e
                      Just e' -> e'

-----------------------------------------------------------------------------------------------------

withTypeEs :: SpecType -> SM [CoreExpr] 
withTypeEs t = do 
    em <- sExprMem <$> get 
    return (map snd3 (filter (\x -> fst3 x == toType False t) em)) 

findCandidates :: Type ->         -- Goal type: Find all candidate expressions of this type,
                                  --   or that produce this type (i.e. functions).
                  SM ExprMemory
findCandidates goalTy = do
  sEMem <- sExprMem <$> get
  return (filter ((goalType goalTy) . fst3) sEMem)

functionCands :: Type -> SM [(Type, GHC.CoreExpr, Int)]
functionCands goalTy = do
  all' <- findCandidates goalTy
  return (filter (isFunction . fst3) all')


---------------------------------------------------------------------------------
--------------------------- Generate error expression ---------------------------
---------------------------------------------------------------------------------

varError :: SM Var
varError = do 
  info      <- ghcI . sCGI <$> get
  let env    = B.makeEnv (gsConfig $ giSpec info) (toGhcSrc $ giSrc info) mempty mempty 
  let name   = giTargetMod $ giSrc info
  let errSym = dummyLoc $ symbol "Language.Haskell.Liquid.Synthesize.Error.err"
  case B.lookupGhcVar env name "Var" errSym of 
    Right v -> return v
    Left e  -> error (show e)
  

toGhcSrc :: TargetSrc -> GhcSrc 
toGhcSrc a = Src
      { _giIncDir    = giIncDir a
      , _giTarget    = giTarget a
      , _giTargetMod = giTargetMod a
      , _giCbs       = giCbs a
      , _gsTcs       = gsTcs a
      , _gsCls       = gsCls a
      , _giDerVars   = giDerVars a
      , _giImpVars   = giImpVars a
      , _giDefVars   = giDefVars a
      , _giUseVars   = giUseVars a
      , _gsExports   = gsExports a
      , _gsFiTcs     = gsFiTcs a
      , _gsFiDcs     = gsFiDcs a
      , _gsPrimTcs   = gsPrimTcs a
      , _gsQualImps  = gsQualImps a
      , _gsAllImps   = gsAllImps a
      , _gsTyThings  = gsTyThings a
      }
