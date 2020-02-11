{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Haskell.Liquid.Synthesize.Monad where


import           Language.Haskell.Liquid.Types hiding (SVar)
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Generate 
import           Language.Haskell.Liquid.Constraint.Env 
import qualified Language.Haskell.Liquid.Types.RefType as R
import           Language.Haskell.Liquid.GHC.Misc (showPpr)
import           Language.Haskell.Liquid.Synthesize.Termination
import           Language.Haskell.Liquid.Synthesize.GHC hiding (SSEnv)
import           Language.Haskell.Liquid.Synthesize.Misc hiding (notrace)
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
import           CoreUtils (exprType)
import qualified Data.HashSet as S
import           Data.Tuple.Extra 

maxMatchDepth :: Int 
maxMatchDepth = 2 

-------------------------------------------------------------------------------
-- | Synthesis Monad ----------------------------------------------------------
-------------------------------------------------------------------------------

-- The state keeps a unique index for generation of fresh variables 
-- and the environment of variables to types that is expanded on lambda terms
type SSEnv = M.HashMap Symbol (SpecType, Var)
type SSDecrTerm = [(Var, [Var])]

-- Initialized with basic type expressions
-- e.g. b  --- x_s3
--     [b] --- [], x_s0, x_s4
type ExprMemory = [(Type, CoreExpr, Int)]
type T = M.HashMap Type (CoreExpr, Int)
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
           , sExprMem   :: ExprMemory 
           , sAppDepth  :: Int
           , sUniVars   :: [Var]
           , sFix       :: Var
           , sGoalTyVar :: Maybe [TyVar]
           , sUGoalTy   :: Maybe [Type] -- ^ Types used for instantiation.
                                        --    Produced by @withUnify@.
           }
type SM = StateT SState IO

-- TODO Write: What is @maxAppDepth@?
maxAppDepth :: Int 
maxAppDepth = 3

locally :: SM a -> SM a 
locally act = do 
  st <- get 
  r <- act 
  modify $ \s -> s{sCGEnv = sCGEnv st, sCGI = sCGI st}
  return r 


evalSM :: SM a -> SMT.Context -> FilePath -> F.Config -> CGInfo -> CGEnv -> REnv -> SSEnv -> SState -> IO a 
evalSM act ctx tgt fcfg cgi cgenv renv env st = do 
  let st' = st {ssEnv = env}
  r <- evalStateT act st'
  SMT.cleanupContext ctx 
  return r 

initState :: SMT.Context -> F.Config -> CGInfo -> CGEnv -> REnv -> Var -> [Var] -> SSEnv -> IO SState 
initState ctx fcfg cgi cgenv renv xtop uniVars env = do
  return $ SState renv env 0 [] ctx cgi cgenv fcfg 0 exprMem0 0 uniVars xtop Nothing Nothing
  where exprMem0 = initExprMem env

getSEnv :: SM SSEnv
getSEnv = ssEnv <$> get 

getSEMem :: SM ExprMemory
getSEMem = sExprMem <$> get

getSFix :: SM Var 
getSFix = sFix <$> get

getSUniVars :: SM [Var]
getSUniVars = sUniVars <$> get

type LEnv = M.HashMap Symbol SpecType -- | Local env.

getLocalEnv :: SM LEnv
getLocalEnv = (reLocal . rEnv) <$> get

getSDecrTerms :: SM SSDecrTerm 
getSDecrTerms = ssDecrTerm <$> get

addsEnv :: [(Var, SpecType)] -> SM () 
addsEnv xts = 
  mapM_ (\(x,t) -> modify (\s -> s {ssEnv = M.insert (symbol x) (t,x) (ssEnv s)})) xts  

addsEmem :: [(Var, SpecType)] -> SM () 
addsEmem xts = do 
  curAppDepth <- sAppDepth <$> get
  mapM_ (\(x,t) -> modify (\s -> s {sExprMem = (toType t, GHC.Var x, curAppDepth) : (sExprMem s)})) xts  
  

addEnv :: Var -> SpecType -> SM ()
addEnv x t = do 
  liftCG0 (\γ -> γ += ("arg", symbol x, t))
  modify (\s -> s {ssEnv = M.insert (symbol x) (t,x) (ssEnv s)}) 

addEmem :: Var -> SpecType -> SM ()
addEmem x t = do 
  let ht0 = toType t
  curAppDepth <- sAppDepth <$> get
  xtop <- getSFix 
  (ht1, _) <- instantiateTL
  let ht = if x == xtop then ht1 else ht0
  modify (\s -> s {sExprMem = (ht, GHC.Var x, curAppDepth) : (sExprMem s)})

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


freshVarType :: Type -> SM Var
freshVarType t = (\i -> mkVar (Just "x") i t) <$> incrSM


freshVar :: SpecType -> SM Var
freshVar = freshVarType . toType

withIncrDepth :: Monoid a => SM a -> SM a
withIncrDepth m = do 
    s <- get 
    let d = sDepth s
    if d + 1 > maxMatchDepth 
      then return mempty
      else do put s{sDepth = d + 1}
              r <- m
              modify $ \s -> s{sDepth = d}
              return r
        
  
incrSM :: SM Int 
incrSM = do s <- get 
            put s{ssIdx = ssIdx s + 1}
            return (ssIdx s)

symbolExpr :: Type -> F.Symbol -> SM CoreExpr 
symbolExpr τ x = incrSM >>= (\i -> return $ F.notracepp ("symExpr for " ++ F.showpp x) $  GHC.Var $ mkVar (Just $ F.symbolString x) i τ)


-- | Initializes @ExprMemory@ structure.
--    1. Transforms refinement types to conventional (Haskell) types.
--    2. All @Depth@s are initialized to 0.
initExprMem :: SSEnv -> ExprMemory
initExprMem sEnv = map (\(_, (t, v)) -> (toType t, GHC.Var v, 0)) (M.toList sEnv)

-- TODO: Fix @SSEnv@ to avoid the hack with the top-level variable.
withInsInitEM :: SSEnv -> SM ExprMemory
withInsInitEM senv = do
  xtop <- getSFix
  (ttop, _) <- instantiateTL
  mbTyVar <- sGoalTyVar <$> get

-- Special handle for the top level variable: No instantiation
  let handleIt e = case e of  GHC.Var v -> if xtop == v then (e, ttop) else change e
                              _         -> change e

      change e = let { e' = instantiate e mbTyVar; t' = exprType e' } in (e', t')

  return $ 
    map (\(t, e, i) -> 
      let (e', t') = handleIt e
      in  (t', e', i)) (initExprMem senv)

insEMem0 :: SSEnv -> SM ExprMemory
insEMem0 senv = do
  xtop <- getSFix
  (ttop, _) <- instantiateTL
  mbUTy <- sUGoalTy <$> get 

-- Special handle for the top level variable: No instantiation
  let handleIt e = case e of  GHC.Var v -> if xtop == v then (e, ttop) else change e
                              _         -> change e

      change e = let { e' = instantiateTy e mbUTy; t' = exprType e' } in (e', t')

  return $ 
    map (\(t, e, i) -> 
      let (e', t') = handleIt e
      in  (t', e', i)) (initExprMem senv)

-- [ TODO ] 
--    Should be for all possible permutations of @mbt@: 
--    instantiate :: CoreExpr -> Maybe [Var] -> [CoreExpr]
instantiate :: CoreExpr -> Maybe [Var] -> CoreExpr
instantiate e mbt = 
  case mbt of
    Nothing     -> e
    Just tyVars -> trace (" Type variables are " ++ show tyVars ++ " expression is " ++ show e) (apply tyVars e)

-- | Applies type variables (1st argument) to an expression.
--   The expression is guaranteed to have the same level of 
--   parametricity (same number of @forall@) as the length of the 1st argument.
--   > The result has zero @forall@.
apply :: [Var] -> GHC.CoreExpr -> GHC.CoreExpr
apply []     e = 
  case exprType e of 
    ForAllTy {} -> error $ " [ instantiate (1) ] For e " ++ show e
    _           -> e
apply (v:vs) e 
  = case exprType e of 
      ForAllTy{} -> apply vs (GHC.App e (GHC.Type (TyVarTy v)))
      _          -> e -- error $ " [ instantiate (2) ] For e " ++ show e ++ " vars = " ++ show (v:vs)

instantiateTy :: CoreExpr -> Maybe [Type] -> CoreExpr
instantiateTy e mbTy = 
  case mbTy of 
    Nothing  -> e
    Just tys -> applyTy tys e

-- | Used for instantiation: Applies types to an expression.
--   > The result does not have @forall@.
applyTy :: [Type] -> GHC.CoreExpr -> GHC.CoreExpr
applyTy []     e =  case exprType e of 
                      ForAllTy{} -> e -- error $ " [ instantiate (1) ] For e " ++ show e
                      _          -> e
applyTy (t:ts) e =  case exprType e of
                      ForAllTy{} -> applyTy ts (GHC.App e (GHC.Type t))
                      _          -> e

-- | Instantiate the top-level variable.
instantiateTL :: SM (Type, GHC.CoreExpr)
instantiateTL = do
  uniVars <- getSUniVars 
  xtop <- getSFix
  let e = apply uniVars (GHC.Var xtop)
  return (exprType e, e)

withInsProdCands :: SpecType -> SM [(Symbol, (Type, Var))]
withInsProdCands specTy = 
  do  senv <- ssEnv <$> get 
      xtop <- getSFix
      (ttop, _) <- instantiateTL
      mbTyVar <- sGoalTyVar <$> get 
      let τ            = toType specTy 
      cands <- findCandidates senv τ 
      let funTyCands'  = filter (isFunction . fst . snd) cands


      -- BOILERPLATE: TODO FIX BOTH
      -- Special handle for the top level variable: No instantiation
      let handleIt e = case e of  GHC.Var v -> if xtop == v then (e, ttop) else change e
                                  _         -> change e

          change e = let { e' = instantiate e mbTyVar; t' = exprType e' } in (e', t')

      return $ map (\(s, (_, v)) -> let (e, ty) = handleIt (GHC.Var v)
                                    in (s, (ty, v))) funTyCands' 

withTypeEs :: String -> SpecType -> SM [CoreExpr] 
withTypeEs s t = do 
    em <- sExprMem <$> get 
    return (map snd3 (filter (\x -> fst3 x == toType t) em)) 


findCandidates :: SSEnv -> Type -> SM [(Symbol, (Type, Var))]
findCandidates senv goalTy = do
  (t0, _) <- instantiateTL
  xtop    <- getSFix
  let s0 = M.toList senv
      s1 = map toTypes s0
      s2 = map change s1

      -- TODO FIX: This is a hack to instantiate top level binder with type variables
      change x@(s, (t, v)) = if v == xtop then (s, (t0, v)) else x
      toTypes (s, (t, v))  = (s, (toType t, v))
      cut (_, (t, v))      = goalType goalTy t  
  return (filter cut s2)
  