{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE BangPatterns #-}
module Language.Haskell.Liquid.Synthesize.Check (check, hasType, isWellTyped, checkError) where


import           Language.Fixpoint.Types.Constraints
import qualified Language.Fixpoint.Types.Config
                                               as F
import qualified Language.Fixpoint.Types       as F
import           Language.Fixpoint.Solver
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Constraint.Generate
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Fresh
                                                ( trueTy )
import           Language.Haskell.Liquid.Constraint.ToFixpoint
import           Language.Haskell.Liquid.Synthesize.Monad
import           Language.Haskell.Liquid.Synthesize.GHC
import           Language.Haskell.Liquid.Misc   ( mapThd3 )
import           CoreSyn
import           Var
import           Control.Monad.State.Lazy
import           System.Console.CmdArgs.Verbosity
import           CoreUtils
import           Language.Haskell.Liquid.GHC.TypeRep
import           Language.Haskell.Liquid.Types
import           MkCore
import           DynFlags
import           Debug.Trace

hasType :: String -> Bool -> SpecType -> CoreExpr -> SM Bool
hasType s b t !e' = notrace (" [ Check ] " ++ show e') $ do 
  x  <- freshVar t 
  st <- get 
  let tpOfE = exprType e'
      ht    = toType t
  if tpOfE == ht
    then do
      r <- liftIO $ quietly $ check (sCGI st) (sCGEnv st) (sFCfg st) x e (Just t) 
      -- liftIO $ putStrLn ("From " ++ s ++ (if b then " Checked:  " else " Well-Typed: ") ++ "Expr = " ++ showPpr (fromAnf e) ++ " of type " ++ show t ++ "\n Res = " ++ show r)
      return r
    else error $ " [ hasType " ++ s ++ " ] Expression = " ++ show e' ++ " with type " ++ showTy tpOfE ++ " , specType = " ++ show t
 where e = tx e' 

-- Returns true if the expression is well-typed.
isWellTyped :: CoreExpr -> SM Bool
isWellTyped e =  do 
  t <- liftCG $ trueTy $ exprType e 
  hasType "" False t e 


tx :: CoreExpr -> CoreExpr
tx (Case e b t alts) = Case e b t (mapThd3 tx <$> alts)
tx e@(Let _ _) = let (bs,e') = unbind e in foldr Let e' bs 
tx e = e 

unbind :: CoreExpr -> ([CoreBind], CoreExpr)
unbind (Let (NonRec x ex) e) = let (bs,e') = unbind ex in (bs ++ [NonRec x e'],e)
unbind e = ([], e)


check :: CGInfo -> CGEnv -> F.Config -> Var -> CoreExpr -> Maybe SpecType -> IO Bool 
check cgi γ cfg x e t = do
    finfo <- cgInfoFInfo info' cs
    isSafe <$> solve cfg{F.srcFile = "SCheck" <> F.srcFile cfg} finfo 
  where 
    cs = generateConstraintsWithEnv info' (cgi{hsCs = []}) (γ{grtys = insertREnv' (F.symbol x) t (grtys γ)}) 
    info' = info {giSrc = giSrc', giSpec = giSpec'}
    giSrc' = (giSrc info) {giCbs = [Rec [(x, e)]]}
    giSpec' = giSpecOld{gsSig = gsSig'}
    giSpecOld = giSpec info 
    gsSigOld  = gsSig giSpecOld
    gsSig' = gsSigOld {gsTySigs = addTySig x t (gsTySigs gsSigOld)}
    info = ghcI cgi 

    insertREnv' x Nothing g = g 
    insertREnv' x (Just t) g = insertREnv x t g
    
    addTySig x Nothing  ts = ts 
    addTySig x (Just t) ts = (x,dummyLoc t):ts
    
checkError :: SpecType -> SM (Maybe CoreExpr)
checkError t = do 
  errVar <- varError
  let errorExpr = App (App (Var errVar) (Type (toType t))) errorInt
      errorInt  = mkIntExprInt unsafeGlobalDynFlags 42
  b <- hasType " checkError " True t errorExpr
  if b 
    then return $ Just errorExpr
    else return Nothing

quietly :: IO a -> IO a
quietly act = do
  vb <- getVerbosity
  setVerbosity Quiet
  r  <- act
  setVerbosity vb
  return r


