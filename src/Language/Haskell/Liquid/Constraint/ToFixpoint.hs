{-# LANGUAGE FlexibleContexts          #-}
module Language.Haskell.Liquid.Constraint.ToFixpoint
  ( cgInfoFInfo
  , fixConfig
  ) where

import           Prelude hiding (error)
import           Data.Monoid

import qualified Language.Fixpoint.Types.Config as FC
import           System.Console.CmdArgs.Default (def)
import qualified Language.Fixpoint.Types        as F
import           Language.Haskell.Liquid.Constraint.Types
import qualified Language.Haskell.Liquid.Types.RefType as RT
import           Language.Haskell.Liquid.Types hiding     ( binds )
import           Language.Fixpoint.Solver                 ( parseFInfo )
import           Language.Haskell.Liquid.Constraint.Qualifier
import Data.Maybe (fromJust)

-- AT: Move to own module?
-- imports for AxiomEnv
import qualified Language.Haskell.Liquid.UX.Config as Config
import           Language.Haskell.Liquid.GHC.Misc  (simplesymbol)
import qualified Data.List                         as L
import qualified Data.HashMap.Strict               as M
import           Data.Maybe                        (fromMaybe)
-- import           Language.Fixpoint.Misc
import qualified Language.Haskell.Liquid.Misc      as Misc
import           Var
import           TyCon                             (TyCon)

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
  , FC.ginteractive     = ginteractive       cfg
  , FC.noslice          = noslice           cfg
  , FC.rewriteAxioms    = Config.allowPLE   cfg
  }


cgInfoFInfo :: GhcInfo -> CGInfo -> IO (F.FInfo Cinfo)
cgInfoFInfo info cgi = do
  let tgtFI  = targetFInfo info cgi
  impFI     <- ignoreQualifiers info <$> parseFInfo (hqFiles info)
  return       (tgtFI <> impFI)

ignoreQualifiers :: GhcInfo -> F.FInfo a -> F.FInfo a
ignoreQualifiers info fi
  | useSpcQuals info = fi
  | otherwise        = fi { F.quals = [] }

targetFInfo :: GhcInfo -> CGInfo -> F.FInfo Cinfo
targetFInfo info cgi = mappend (mempty { F.ae = ax }) fi
  where
    fi               = F.fi cs ws bs ls consts ks qs bi aHO aHOqs es mempty adts
    cs               = fixCs    cgi
    ws               = fixWfs   cgi
    bs               = binds    cgi
    ls               = fEnv     cgi
    consts           = cgConsts cgi
    ks               = kuts     cgi
    adts             = cgADTs   cgi
    qs               = qualifiers info (fEnv cgi)
    bi               = (\x -> Ci x Nothing Nothing) <$> bindSpans cgi
    aHO              = allowHO cgi
    aHOqs            = higherOrderFlag info
    es               = [] -- makeAxioms info
    ax               = makeAxiomEnvironment info (dataConTys cgi) (F.cm fi)
    -- msg              = show . map F.symbol . M.keys . tyConInfo

makeAxiomEnvironment :: GhcInfo -> [(Var, SpecType)] -> M.HashMap F.SubcId (F.SubC Cinfo) -> F.AxiomEnv
makeAxiomEnvironment info xts fcs
  = F.AEnv (makeEquations sp ++ [specTypeEq emb x t | (x, t) <- xts])
           (concatMap makeSimplify xts)
           (doExpand sp cfg <$> fcs)
  where
    emb      = gsTcEmbeds sp
    cfg      = getConfig  info
    sp       = spec       info

doExpand :: GhcSpec -> Config -> F.SubC Cinfo -> Bool
doExpand sp cfg sub = Config.allowGlobalPLE cfg
                   || (Config.allowLocalPLE cfg && maybe False (`M.member` gsAutoInst sp) (subVar sub))

specTypeEq :: F.TCEmb TyCon -> Var -> SpecType -> F.Equation
specTypeEq emb f t = F.mkEquation (F.symbol f) xts body tOut
  where
    xts            = Misc.safeZipWithError "specTypeEq" xs (RT.rTypeSort emb <$> ts)
    body           = specTypeToResultRef bExp t
    tOut           = RT.rTypeSort emb (ty_res tRep)
    tRep           = toRTypeRep t
    xs             = ty_binds tRep
    ts             = ty_args  tRep
    bExp           = F.eApps (F.eVar f) (F.EVar <$> xs)

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

makeEquations :: GhcSpec -> [F.Equation]
makeEquations sp = [ F.mkEquation f xts (equationBody (F.EVar f) xArgs e mbT) t
                      | F.Equ f xts e t _ <- gsAxioms sp
                      , let mbT            = M.lookup f sigs
                      , let xArgs          = F.EVar . fst <$> xts
                   ]
  where
    sigs         = M.fromList [ (simplesymbol v, t) | (v, t) <- gsTySigs sp ]

equationBody :: F.Expr -> [F.Expr] -> F.Expr -> Maybe LocSpecType -> F.Expr
equationBody f xArgs e mbT
  | Just t <- mbT = F.pAnd [eBody, rBody t]
  | otherwise     = eBody
  where
    eBody         = F.PAtom F.Eq (F.eApps f xArgs) e
    rBody t       = specTypeToLogic xArgs (F.eApps f xArgs) (val t)

-- NV Move this to types?
-- sound but imprecise approximation of a type in the logic
specTypeToLogic :: [F.Expr] -> F.Expr -> SpecType -> F.Expr
specTypeToLogic es e t
  | ok        = F.subst su (F.PImp (F.pAnd args) res)
  | otherwise = F.PTrue
  where
    res       = specTypeToResultRef e t
    args      = zipWith mkExpr (mkReft <$> ts) es
    mkReft t  =  F.toReft $ fromMaybe mempty (stripRTypeBase t)
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
