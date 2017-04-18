{-# LANGUAGE FlexibleContexts          #-}
module Language.Haskell.Liquid.Constraint.ToFixpoint (

    cgInfoFInfo

  , fixConfig

  ) where

import           Prelude hiding (error)
import           Data.Monoid

import qualified Language.Fixpoint.Types.Config as FC
import           System.Console.CmdArgs.Default (def)
import qualified Language.Fixpoint.Types        as F
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Types hiding     ( binds )
import           Language.Fixpoint.Solver                 ( parseFInfo )
import           Language.Haskell.Liquid.Constraint.Qualifier
-- import           Language.Fixpoint.Misc (traceShow)

import Language.Haskell.Liquid.UX.Config (allowSMTInstationation)
import Data.Maybe (fromJust)

-- AT: Move to own module?
-- imports for AxiomEnv
import           Language.Haskell.Liquid.UX.Config (allowLiquidInstationationGlobal, allowLiquidInstationationLocal, allowRewrite, allowArithmetic)
import           Language.Haskell.Liquid.GHC.Misc  (dropModuleNames, simplesymbol)
import qualified Data.List                         as L
import qualified Data.HashMap.Strict               as M
import           Data.Maybe                        (fromMaybe)
import           Language.Fixpoint.Misc
import           Var

fixConfig :: FilePath -> Config -> FC.Config
fixConfig tgt cfg = def
  { FC.solver           = fromJust (smtsolver cfg)
  , FC.linear           = linear            cfg
  , FC.eliminate        = eliminate         cfg
  , FC.nonLinCuts       = not (higherOrderFlag cfg) -- eliminate cfg /= FC.All
  , FC.save             = saveQuery         cfg
  , FC.srcFile          = tgt
  , FC.cores            = cores             cfg
  , FC.minPartSize      = minPartSize       cfg
  , FC.maxPartSize      = maxPartSize       cfg
  , FC.elimStats        = elimStats         cfg
  , FC.elimBound        = elimBound         cfg
  , FC.allowHO          = higherOrderFlag   cfg
  , FC.allowHOqs        = higherorderqs     cfg
  , FC.extensionality   = extensionality    cfg || gradual cfg
  , FC.alphaEquivalence = alphaEquivalence  cfg
  , FC.betaEquivalence  = betaEquivalence   cfg
  , FC.normalForm       = normalForm        cfg
  , FC.stringTheory     = stringTheory      cfg
  , FC.gradual          = gradual           cfg 
  }


cgInfoFInfo :: GhcInfo -> CGInfo -> IO (F.FInfo Cinfo)
cgInfoFInfo info cgi = do
  let tgtFI  = targetFInfo info cgi
  impFI     <- ignoreQualifiers info <$> parseFInfo (hqFiles info)
  return       (tgtFI <> impFI)
  -- let fI    = ignoreQualifiers info (tgtFI <> impFI)
  -- return fI

ignoreQualifiers :: GhcInfo -> F.FInfo a -> F.FInfo a
ignoreQualifiers info fi
  | useSpcQuals info = fi
  | otherwise        = fi { F.quals = [] }

-- NOPROP ignoreQualifiers :: GhcInfo -> F.FInfo a -> F.FInfo a
-- NOPROP ignoreQualifiers info fi
  -- NOPROP | noQuals     = fi { F.quals = [] }
  -- NOPROP | otherwise   = fi
  -- NOPROP where noQuals = (FC.All == ) . eliminate . getConfig . spec $ info

targetFInfo :: GhcInfo -> CGInfo -> F.FInfo Cinfo
targetFInfo info cgi = mappend (mempty { F.ae = ax }) fi
  where
    fi               = F.fi cs ws bs ls consts ks qs bi aHO aHOqs es mempty
    cs               = fixCs    cgi
    ws               = fixWfs   cgi
    bs               = binds    cgi
    ls               = fEnv     cgi
    consts           = cgConsts cgi
    ks               = kuts     cgi
    qs               = qualifiers info (fEnv cgi)
    bi               = (\x -> Ci x Nothing Nothing) <$> bindSpans cgi
    aHO              = allowHO cgi
    aHOqs            = higherOrderFlag info
    es               = makeAxioms info
    ax               = makeAxiomEnvironment info (dataConTys cgi) (F.cm fi)

makeAxiomEnvironment :: GhcInfo -> [(Var, SpecType)] -> M.HashMap F.SubcId (F.SubC Cinfo) -> F.AxiomEnv
makeAxiomEnvironment info xts fcs
  = F.AEnv ((axiomName <$> gsAxioms (spec info)) ++ (F.symbol . fst <$> xts))
           (makeEquations info ++ (specTypToEq  <$> xts))
           (concatMap makeSimplify xts)
           fuelMap
           doExpand
           (allowRewrite    cfg)
           (allowArithmetic cfg)
           (debugInstantionation cfg)
           fixCfg
  where
    cfg = getConfig info
    fixCfg = fixConfig fileName cfg
    fileName = head (files cfg)  ++ ".evals"
    doExpand = (\sub -> (allowLiquidInstationationGlobal cfg
                || (allowLiquidInstationationLocal cfg
                && (maybe False (`M.member` (gsAutoInst (spec info))) (subVar sub)))))
                            <$> fcs
    fuelNumber sub = do {v <- subVar sub; lp <- M.lookup v (gsAutoInst (spec info)); lp}
    fuelMap = (\sub -> (fromMaybe (fuel cfg) (fuelNumber sub))) <$> fcs
    specTypToEq (x, t)
      = F.Equ (F.symbol x) (ty_binds $ toRTypeRep t)
           (specTypeToResultRef (F.eApps (F.EVar $ F.symbol x) (F.EVar <$> ty_binds (toRTypeRep t))) t)

makeSimplify :: (Var, SpecType) -> [F.Rewrite]
makeSimplify (x, t) = go $ specTypeToResultRef (F.eApps (F.EVar $ F.symbol x) (F.EVar <$> ty_binds (toRTypeRep t))) t
  where
    go (F.PAnd es) = concatMap go es

    go (F.PAtom eq (F.EApp (F.EVar f) dc) bd)
      | eq `elem` [F.Eq, F.Ueq]
      , (F.EVar dc, xs) <- F.splitEApp dc
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) bd]

    go (F.PIff (F.EApp (F.EVar f) dc) bd)
      | (F.EVar dc, xs) <- F.splitEApp dc
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) bd]

    go _ = []

    isEVar (F.EVar _) = True
    isEVar _ = False

    fromEVar (F.EVar x) = x
    fromEVar _ = impossible Nothing "makeSimplify.fromEVar"

makeEquations :: GhcInfo -> [F.Equation]
makeEquations info
  = [ F.Equ x xs (F.pAnd [makeEqBody x xs e, makeRefBody x xs (lookupSpecType x (gsTySigs $ spec info))]) | AxiomEq x xs e _ <- gsAxioms (spec info)]
  where
    makeEqBody x xs e = F.PAtom F.Eq (F.eApps (F.EVar x) (F.EVar <$> xs)) e
    lookupSpecType x xts = L.lookup x ((mapFst (dropModuleNames . simplesymbol)) <$> xts)
    makeRefBody _ _  Nothing  = F.PTrue
    makeRefBody x xs (Just t) = specTypeToLogic (F.EVar <$> xs) (F.eApps (F.EVar x) (F.EVar <$> xs)) (val t)


-- NV Move this to types?
-- sound but imprecise approximation of a tyep in the logic
specTypeToLogic :: [F.Expr] -> F.Expr -> SpecType -> F.Expr
specTypeToLogic es e t
  | ok        = F.subst su (F.PImp (F.pAnd args) res)
  | otherwise = F.PTrue
  where
    res     = specTypeToResultRef e t

    args    = zipWith mkExpr (mkReft <$> ts) es

    mkReft t =  F.toReft $ fromMaybe mempty (stripRTypeBase t)
    mkExpr (F.Reft (v, ev)) e = F.subst1 ev (v, e)


    ok      = okLen && okClass && okArgs
    okLen   = length xs == length xs
    okClass = all (F.isTauto . snd) cls
    okArgs  = all okArg ts

    okArg (RVar _ _)       = True
    okArg t@(RApp _ _ _ _) = F.isTauto (t{rt_reft = mempty})
    okArg _                = False


    su           = F.mkSubst $ zip xs es
    (cls, nocls) = L.partition (isClassType.snd) $ zip (ty_binds trep) (ty_args trep)
                 :: ([(F.Symbol, SpecType)], [(F.Symbol, SpecType)])
    (xs, ts)     = unzip nocls :: ([F.Symbol], [SpecType])

    trep = toRTypeRep t


specTypeToResultRef :: F.Expr -> SpecType -> F.Expr
specTypeToResultRef e t
  = mkExpr $ F.toReft $ fromMaybe mempty (stripRTypeBase $ ty_res trep)
  where
    mkExpr (F.Reft (v, ev)) = F.subst1 ev (v, e)
    trep                   = toRTypeRep t

makeAxioms :: GhcInfo -> [F.Triggered F.Expr]
makeAxioms info 
  | allowSMTInstationation (getConfig info)
  = F.defaultTrigger . axiomEq <$> gsAxioms (spec info)
  | otherwise
  = [] 
