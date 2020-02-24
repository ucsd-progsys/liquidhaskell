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
import           Data.Maybe
import           Debug.Trace 
import           Language.Haskell.Liquid.GHC.TypeRep
import           Data.List 
import           Language.Fixpoint.Types.PrettyPrint
import           Data.Tuple.Extra

synthesize :: FilePath -> F.Config -> CGInfo -> IO [Error]
synthesize tgt fcfg cginfo = 
  mapM go (M.toList $ holesMap cginfo)
  where 
    go (x, HoleInfo t loc env (cgi,cge)) = do 
      let topLvlBndr = fromMaybe (error "Top-level binder not found") (cgVar cge)
          typeOfTopLvlBnd = fromMaybe (error "Type: Top-level symbol not found") (M.lookup (symbol topLvlBndr) (reGlobal env))
          coreProgram = giCbs $ giSrc $ ghcI cgi
          (uniVars, _) = getUniVars coreProgram topLvlBndr
          fromREnv = filterREnv (reLocal env)
          ssenv0 = symbolToVar coreProgram topLvlBndr fromREnv
          (senv1, foralls) = initSSEnv typeOfTopLvlBnd cginfo ssenv0
      
      ctx <- SMT.makeContext fcfg tgt
      state0 <- initState ctx fcfg cgi cge env topLvlBndr (reverse uniVars) M.empty

      fills <- synthesize' tgt ctx fcfg cgi cge env senv1 x typeOfTopLvlBnd topLvlBndr typeOfTopLvlBnd foralls state0

      return $ ErrHole loc (
        if not (null fills)
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

    go (RAllP _ t) = go t

    go (RRTy env ref obl t) = go t

    go t@(RFun{}) 
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
              mapM (\y -> addDecrTerm y []) ys
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
  em <- getSEMem
  let es0 = [((e, t, c), d) | ( t@(TyConApp c _), e, d ) <- em]
      es1 = filter (not . trivial . fst3 . fst) es0
      es42 = filter (appOnly . fst3 .fst) es1

      -- es' = filter (noLet . fst3 . fst) es1
      -- es2 = filter (noPairLike . fst) es'
      -- es3 = sortOn snd es2
      es3 = sortOn snd es42
      es4 = map fst es3
      -- es5 = filter (not . isClassTyCon . thd3) es4
  return es4 -- (filter (isVar . fst3) es1)

appOnly :: GHC.CoreExpr -> Bool
appOnly (GHC.Var{}) = True
appOnly (GHC.Type{}) = True
appOnly (GHC.App e1 e2) = appOnly e1 && appOnly e2
appOnly _ = False 

noLet :: GHC.CoreExpr -> Bool
noLet (GHC.Let{}) = False
noLet _ = True

noPairLike :: (GHC.CoreExpr, Type, TyCon) -> Bool
noPairLike (e, t, c) = 
  if length (tyConDataCons c) > 1 
    then True
    else inspect e (tyConDataCons c)

inspect :: GHC.CoreExpr -> [DataCon] -> Bool
inspect e [dataCon] 
  = not $ outer e == dataConWorkId dataCon
inspect _ _  
  = False -- error " Should be a singleton. "

outer :: GHC.CoreExpr -> Var
outer (GHC.Var v)
  = v
outer (GHC.App e1 e2)
  = outer e1
outer e = error (" [ outer ] " ++ show e)

isVar :: GHC.CoreExpr -> Bool
isVar (GHC.Var _) = True
isVar _ = False

matchOnExpr :: String -> SpecType -> (CoreExpr, Type, TyCon) -> SM [CoreExpr]
matchOnExpr s t (GHC.Var v, tx, c) 
  = matchOn s t (v, tx, c)
matchOnExpr s t (e, tx, c)
  = do  freshV <- freshVarType tx
        freshSpecTy <- liftCG $ trueTy tx
        addEnv freshV freshSpecTy
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
  addDecrTerm x xs
  liftCG0 (\γ -> caseEnv γ x mempty (GHC.DataAlt c) xs Nothing)
  es <- synthesizeBasic TermGen (s ++ " makeAlt for " ++ show c ++ " with vars " ++ show xs ++ " for t " ++ show t) t
  return $ (\e -> (GHC.DataAlt c, xs, e)) <$> es
  where 
    (_, _, τs) = dataConInstSig c ts -- (toType <$> ts)
makeAlt s _ _ _ _ = error $ "makeAlt.bad argument " ++ s
