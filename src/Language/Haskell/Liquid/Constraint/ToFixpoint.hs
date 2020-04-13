{-# LANGUAGE FlexibleContexts          #-}
module Language.Haskell.Liquid.Constraint.ToFixpoint
  ( cgInfoFInfo
  , fixConfig
  ) where

import           Prelude hiding (error)
import qualified Language.Haskell.Liquid.GHC.API as Ghc
import qualified Language.Fixpoint.Types.Config as FC
import           System.Console.CmdArgs.Default (def)
import qualified Language.Fixpoint.Types        as F
import           Language.Haskell.Liquid.Constraint.Types
import qualified Language.Haskell.Liquid.Types.RefType as RT
import           Language.Haskell.Liquid.Constraint.Qualifier
import qualified Data.Maybe as Mb 

-- AT: Move to own module?
-- imports for AxiomEnv
import qualified Language.Haskell.Liquid.UX.Config as Config
import qualified Language.Haskell.Liquid.GHC.Misc  as GM -- (simplesymbol)
import qualified Data.List                         as L
import qualified Data.HashMap.Strict               as M
import qualified Data.HashSet                      as S
-- import           Language.Fixpoint.Misc
import qualified Language.Haskell.Liquid.Misc      as Misc
import           Var
import           TyCon                             (TyCon)

import           Language.Haskell.Liquid.Types hiding     ( binds )

fixConfig :: FilePath -> Config -> FC.Config
fixConfig tgt cfg = def
  { FC.solver           = Mb.fromJust (smtsolver cfg)
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
  , FC.smtTimeout       = smtTimeout        cfg 
  , FC.stringTheory     = stringTheory      cfg
  , FC.gradual          = gradual           cfg
  , FC.ginteractive     = ginteractive       cfg
  , FC.noslice          = noslice           cfg
  , FC.rewriteAxioms    = Config.allowPLE   cfg
  , FC.etaElim          = not (exactDC cfg) && extensionality cfg -- SEE: https://github.com/ucsd-progsys/liquidhaskell/issues/1601
  , FC.extensionality   = extensionality    cfg 
  , FC.oldPLE           = oldPLE cfg
  }


cgInfoFInfo :: TargetInfo -> CGInfo -> IO (F.FInfo Cinfo)
cgInfoFInfo info cgi = return (targetFInfo info cgi)

targetFInfo :: TargetInfo -> CGInfo -> F.FInfo Cinfo
targetFInfo info cgi = mappend (mempty { F.ae = ax }) fi
  where
    fi               = F.fi cs ws bs ls consts ks qs bi aHO aHOqs es mempty adts ebs
    cs               = fixCs    cgi
    ws               = fixWfs   cgi
    bs               = binds    cgi
    ebs              = ebinds   cgi
    ls               = fEnv     cgi
    consts           = cgConsts cgi
    ks               = kuts     cgi
    adts             = cgADTs   cgi
    qs               = giQuals info (fEnv cgi)
    bi               = (\x -> Ci x Nothing Nothing) <$> bindSpans cgi
    aHO              = allowHO cgi
    aHOqs            = higherOrderFlag info
    es               = [] -- makeAxioms info
    ax               = makeAxiomEnvironment info (dataConTys cgi) (F.cm fi)
    -- msg              = show . map F.symbol . M.keys . tyConInfo

makeAxiomEnvironment :: TargetInfo -> [(Var, SpecType)] -> M.HashMap F.SubcId (F.SubC Cinfo) -> F.AxiomEnv
makeAxiomEnvironment info xts fcs
  = F.AEnv eqs  
           (concatMap makeSimplify xts)
           (doExpand sp cfg <$> fcs)
           (makeRewrites info <$> fcs)
  where
    eqs      = if (oldPLE cfg) 
                then (makeEquations sp ++ map (uncurry $ specTypeEq emb) xts)
                else axioms  
    emb      = gsTcEmbeds (gsName sp)
    cfg      = getConfig  info
    sp       = giSpec     info
    axioms   = gsMyAxioms refl ++ gsImpAxioms refl 
    refl     = gsRefl sp


makeRewrites :: TargetInfo -> F.SubC Cinfo -> [F.AutoRewrite]
makeRewrites info sub = concatMap makeRewriteOne $ filter ((`S.member` rws) . fst) sigs
  where
    sigs    =             gsTySigs   $ gsSig  $ giSpec info 
    isGlobalRw = Mb.maybe False (`elem` globalRws) (subVar sub)

    rws        =
      if isGlobalRw
      then S.empty
      else S.difference (S.union localRws globalRws) (Mb.maybe S.empty S.singleton (subVar sub))

    localRws = Mb.fromMaybe S.empty $ do
      var <- subVar sub
      usable <- M.lookup var $ gsRewritesWith $ gsRefl $ giSpec info
      return $ S.fromList usable
    globalRws  = S.map val $ gsRewrites $ gsRefl $ giSpec info 

makeRewriteOne :: (Var,LocSpecType) -> [F.AutoRewrite]
makeRewriteOne (_,t)
  | Just r <- stripRTypeBase tres
  = concatMap id [
      [F.AutoRewrite xs lhs rhs, F.AutoRewrite xs rhs lhs] |
      F.EEq lhs rhs <- F.splitPAnd $ F.reftPred (F.toReft r) ]
  | otherwise
  = [] 
  where 
    xs = ty_binds tRep
    tres = ty_res tRep
    tRep = toRTypeRep $ val t 

_isClassOrDict :: Id -> Bool
_isClassOrDict x = F.tracepp ("isClassOrDict: " ++ F.showpp x) 
                    $ (hasClassArg x || GM.isDictionary x || Mb.isJust (Ghc.isClassOpId_maybe x))

hasClassArg :: Id -> Bool
hasClassArg x = F.tracepp msg $ (GM.isDataConId x && any Ghc.isClassPred (t:ts))
  where 
    msg       = "hasClassArg: " ++ showpp (x, t:ts)
    (ts, t)   = Ghc.splitFunTys . snd . Ghc.splitForAllTys . Ghc.varType $ x


doExpand :: TargetSpec -> Config -> F.SubC Cinfo -> Bool
doExpand sp cfg sub = Config.allowGlobalPLE cfg
                   || (Config.allowLocalPLE cfg && maybe False (isPLEVar sp) (subVar sub))

-- [TODO:missing-sorts] data-constructors often have unelaboratable 'define' so either
-- 1. Make `elaborate` robust so it doesn't crash and returns maybe or
-- 2. Make the `ctor` well-sorted or 
-- 3. Don't create `define` for the ctor. 
-- Unfortunately 3 breaks a bunch of tests...

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
makeSimplify (x, t)
  | not (GM.isDataConId x)
  = [] 
  | otherwise 
  = go $ specTypeToResultRef (F.eApps (F.EVar $ F.symbol x) (F.EVar <$> ty_binds (toRTypeRep t))) t
  where
    go (F.PAnd es) = concatMap go es

    go (F.PAtom eq (F.EApp (F.EVar f) dc) bd)
      | eq `elem` [F.Eq, F.Ueq]
      , (F.EVar dc, xs) <- F.splitEApp dc
      , dc == F.symbol x 
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) bd]

    go (F.PIff (F.EApp (F.EVar f) dc) bd)
      | (F.EVar dc, xs) <- F.splitEApp dc
      , dc == F.symbol x 
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) bd]

    go _ = []

    isEVar (F.EVar _) = True
    isEVar _ = False

    fromEVar (F.EVar x) = x
    fromEVar _ = impossible Nothing "makeSimplify.fromEVar"

makeEquations :: TargetSpec -> [F.Equation]
makeEquations sp = [ F.mkEquation f xts (equationBody (F.EVar f) xArgs e mbT) t
                      | F.Equ f xts e t _ <- axioms 
                      , let xArgs          = F.EVar . fst <$> xts
                      , let mbT            = if null xArgs then Nothing else M.lookup f sigs
                   ]
  where
    axioms       = gsMyAxioms refl ++ gsImpAxioms refl 
    refl         = gsRefl sp
    sigs         = M.fromList [ (GM.simplesymbol v, t) | (v, t) <- gsTySigs (gsSig sp) ]

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
    mkReft t  =  F.toReft $ Mb.fromMaybe mempty (stripRTypeBase t)
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
  = mkExpr $ F.toReft $ Mb.fromMaybe mempty (stripRTypeBase $ ty_res trep)
  where
    mkExpr (F.Reft (v, ev)) = F.subst1 ev (v, e)
    trep                   = toRTypeRep t
