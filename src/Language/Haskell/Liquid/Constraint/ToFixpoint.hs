{-# LANGUAGE FlexibleContexts          #-}
module Language.Haskell.Liquid.Constraint.ToFixpoint
  ( cgInfoFInfo
  , fixConfig
  , refinementEQs
  , canRewrite
  ) where

import           Prelude hiding (error)
import qualified Language.Haskell.Liquid.GHC.API as Ghc
import           Language.Haskell.Liquid.GHC.API (Var, Id, TyCon)
import qualified Language.Fixpoint.Types.Config as FC
import           System.Console.CmdArgs.Default (def)
import qualified Language.Fixpoint.Types        as F
import           Language.Fixpoint.Solver.Rewrite (unify)
import           Language.Haskell.Liquid.Constraint.Types
import qualified Language.Haskell.Liquid.Types.RefType as RT
import           Language.Haskell.Liquid.Constraint.Qualifier
import           Control.Monad (guard)
import qualified Data.Maybe as Mb

-- AT: Move to own module?
-- imports for AxiomEnv
import qualified Language.Haskell.Liquid.UX.Config as Config
import           Language.Haskell.Liquid.UX.DiffCheck (coreDefs, coreDeps, dependsOn, Def(..))
import qualified Language.Haskell.Liquid.GHC.Misc  as GM -- (simplesymbol)
import qualified Data.List                         as L
import qualified Data.HashMap.Strict               as M
import qualified Data.HashSet                      as S
-- import           Language.Fixpoint.Misc
import qualified Language.Haskell.Liquid.Misc      as Misc

import           Language.Haskell.Liquid.Types hiding     ( binds )

fixConfig :: FilePath -> Config -> FC.Config
fixConfig tgt cfg = def
  { FC.solver                   = Mb.fromJust (smtsolver cfg)
  , FC.linear                   = linear            cfg
  , FC.eliminate                = eliminate         cfg
  , FC.nonLinCuts               = not (higherOrderFlag cfg) -- eliminate cfg /= FC.All
  , FC.save                     = saveQuery         cfg
  , FC.srcFile                  = tgt
  , FC.cores                    = cores             cfg
  , FC.minPartSize              = minPartSize       cfg
  , FC.maxPartSize              = maxPartSize       cfg
  , FC.elimStats                = elimStats         cfg
  , FC.elimBound                = elimBound         cfg
  , FC.allowHO                  = higherOrderFlag   cfg
  , FC.allowHOqs                = higherorderqs     cfg
  , FC.smtTimeout               = smtTimeout        cfg 
  , FC.stringTheory             = stringTheory      cfg
  , FC.gradual                  = gradual           cfg
  , FC.ginteractive             = ginteractive       cfg
  , FC.noslice                  = noslice           cfg
  , FC.rewriteAxioms            = Config.allowPLE   cfg
  , FC.etaElim                  = not (exactDC cfg) && extensionality cfg -- SEE: https://github.com/ucsd-progsys/liquidhaskell/issues/1601
  , FC.extensionality           = extensionality    cfg 
  , FC.useInterpreter           = useInterpreter    cfg
  , FC.oldPLE                   = oldPLE cfg
  , FC.rwTerminationCheck       = rwTerminationCheck cfg
  , FC.noLazyPLE                = noLazyPLE cfg
  , FC.fuel                     = fuel      cfg
  , FC.noEnvironmentReduction   = not (environmentReduction cfg)
  , FC.inlineANFBindings        = inlineANFBindings cfg
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
    eqs      = if oldPLE cfg
                then makeEquations (typeclass cfg) sp ++ map (uncurry $ specTypeEq emb) xts
                else axioms  
    emb      = gsTcEmbeds (gsName sp)
    cfg      = getConfig  info
    sp       = giSpec     info
    axioms   = gsMyAxioms refl ++ gsImpAxioms refl 
    refl     = gsRefl sp


makeRewrites :: TargetInfo -> F.SubC Cinfo -> [F.AutoRewrite]
makeRewrites info sub = concatMap (makeRewriteOne tce) $ filter ((`S.member` rws) . fst) sigs
  where
    tce        = gsTcEmbeds (gsName spec)
    spec       = giSpec info
    sig        = gsSig spec
    sigs       = gsTySigs sig ++ gsAsmSigs sig
    isGlobalRw = Mb.maybe False (`elem` globalRws) parentFunction

    parentFunction :: Maybe Var
    parentFunction =
      case subVar sub of
        Just v -> Just v
        Nothing ->
          Mb.listToMaybe $ do
            D s e v <- coreDefs $ giCbs $ giSrc info
            let (Ghc.RealSrcSpan cc _) = (ci_loc $ F.sinfo sub)
            guard $ s <= Ghc.srcSpanStartLine cc && e >= Ghc.srcSpanEndLine cc
            return v

    rws =
      if isGlobalRw
      then S.empty
      else S.difference
        (S.union localRws globalRws)
        (Mb.maybe S.empty forbiddenRWs parentFunction)

    allDeps         = coreDeps $ giCbs $ giSrc info
    forbiddenRWs sv =
      S.insert sv $ dependsOn allDeps [sv]

    localRws = Mb.fromMaybe S.empty $ do
      var    <- parentFunction
      usable <- M.lookup var $ gsRewritesWith $ gsRefl spec
      return $ S.fromList usable

    globalRws = S.map val $ gsRewrites $ gsRefl spec


canRewrite :: S.HashSet F.Symbol -> F.Expr -> F.Expr -> Bool
canRewrite freeVars from to = noFreeSyms && doesNotDiverge
  where
    fromSyms           = S.intersection freeVars (S.fromList $ F.syms from)
    toSyms             = S.intersection freeVars (S.fromList $ F.syms to)
    noFreeSyms         = S.null $ S.difference toSyms fromSyms
    doesNotDiverge     = Mb.isNothing (unify (S.toList freeVars) from to)
                      || Mb.isJust (unify (S.toList freeVars) to from)

refinementEQs :: LocSpecType -> [(F.Expr, F.Expr)]
refinementEQs t =
  case stripRTypeBase tres of
    Just r ->
      [ (lhs, rhs) | (F.EEq lhs rhs) <- F.splitPAnd $ F.reftPred (F.toReft r) ]
    Nothing ->
      []
  where
    tres = ty_res tRep
    tRep = toRTypeRep $ val t 
  
makeRewriteOne :: (F.TCEmb TyCon) -> (Var, LocSpecType) -> [F.AutoRewrite]
makeRewriteOne tce (_, t)
  = [rw | (lhs, rhs) <- refinementEQs t , rw <- rewrites lhs rhs ]
  where

    rewrites :: F.Expr -> F.Expr -> [F.AutoRewrite]
    rewrites lhs rhs =
         (guard (canRewrite freeVars lhs rhs) >> [F.AutoRewrite xs lhs rhs])
      ++ (guard (canRewrite freeVars rhs lhs) >> [F.AutoRewrite xs rhs lhs])

    freeVars = S.fromList (ty_binds tRep)

    xs = do
      (sym, arg) <- zip (ty_binds tRep) (ty_args tRep)
      let e = maybe F.PTrue (F.reftPred . F.toReft) (stripRTypeBase arg)
      return $ F.RR (rTypeSort tce arg) (F.Reft (sym, e))
       
    tRep = toRTypeRep $ val t 

_isClassOrDict :: Id -> Bool
_isClassOrDict x = F.tracepp ("isClassOrDict: " ++ F.showpp x) 
                    $ (hasClassArg x || GM.isDictionary x || Mb.isJust (Ghc.isClassOpId_maybe x))

hasClassArg :: Id -> Bool
hasClassArg x = F.tracepp msg $ (GM.isDataConId x && any Ghc.isClassPred (t:ts'))
  where 
    msg       = "hasClassArg: " ++ showpp (x, t:ts')
    (ts, t)   = Ghc.splitFunTys . snd . Ghc.splitForAllTys . Ghc.varType $ x
    ts'       = map Ghc.irrelevantMult ts


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

    go (F.EApp (F.EVar f) dc)
      | (F.EVar dc, xs) <- F.splitEApp dc
      , dc == F.symbol x
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) F.PTrue]

    go (F.PNot (F.EApp (F.EVar f) dc))
      | (F.EVar dc, xs) <- F.splitEApp dc
      , dc == F.symbol x
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) F.PFalse]

    go _ = []

    isEVar (F.EVar _) = True
    isEVar _ = False

    fromEVar (F.EVar x) = x
    fromEVar _ = impossible Nothing "makeSimplify.fromEVar"

makeEquations :: Bool -> TargetSpec -> [F.Equation]
makeEquations allowTC sp = [ F.mkEquation f xts (equationBody allowTC (F.EVar f) xArgs e mbT) t
                      | F.Equ f xts e t _ <- axioms 
                      , let xArgs          = F.EVar . fst <$> xts
                      , let mbT            = if null xArgs then Nothing else M.lookup f sigs
                   ]
  where
    axioms       = gsMyAxioms refl ++ gsImpAxioms refl 
    refl         = gsRefl sp
    sigs         = M.fromList [ (GM.simplesymbol v, t) | (v, t) <- gsTySigs (gsSig sp) ]

equationBody :: Bool -> F.Expr -> [F.Expr] -> F.Expr -> Maybe LocSpecType -> F.Expr
equationBody allowTC f xArgs e mbT
  | Just t <- mbT = F.pAnd [eBody, rBody t]
  | otherwise     = eBody
  where
    eBody         = F.PAtom F.Eq (F.eApps f xArgs) e
    rBody t       = specTypeToLogic allowTC xArgs (F.eApps f xArgs) (val t)

-- NV Move this to types?
-- sound but imprecise approximation of a type in the logic
specTypeToLogic :: Bool -> [F.Expr] -> F.Expr -> SpecType -> F.Expr
specTypeToLogic allowTC es e t
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
    (cls, nocls) = L.partition ((if allowTC then isEmbeddedClass else isClassType).snd) $ zip (ty_binds trep) (ty_args trep)
                 :: ([(F.Symbol, SpecType)], [(F.Symbol, SpecType)])
    (xs, ts)     = unzip nocls :: ([F.Symbol], [SpecType])

    trep = toRTypeRep t


specTypeToResultRef :: F.Expr -> SpecType -> F.Expr
specTypeToResultRef e t
  = mkExpr $ F.toReft $ Mb.fromMaybe mempty (stripRTypeBase $ ty_res trep)
  where
    mkExpr (F.Reft (v, ev)) = F.subst1 ev (v, e)
    trep                   = toRTypeRep t
