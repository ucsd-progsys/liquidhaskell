{-# LANGUAGE FlexibleContexts          #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Language.Haskell.Liquid.Constraint.ToFixpoint
  ( cgInfoFInfo
  , fixConfig
  , refinementEQs
  , canRewrite
  ) where

import           Prelude hiding (error)
import qualified Liquid.GHC.API as Ghc
import           Liquid.GHC.API (Var, Id, TyCon)
import qualified Language.Fixpoint.Types.Config as FC
import qualified Language.Fixpoint.Types        as F
import           Language.Fixpoint.Solver.Rewrite (unify)
import           Language.Haskell.Liquid.Constraint.Types
import qualified Language.Haskell.Liquid.Types.RefType as RT
import           Language.Haskell.Liquid.Constraint.Qualifier
import           Control.Monad (guard)
import qualified Data.Maybe as Mb

-- AT: Move to own module?
-- imports for AxiomEnv
import           Language.Haskell.Liquid.UX.Config
import           Language.Haskell.Liquid.UX.DiffCheck (coreDefs, coreDeps, dependsOn, Def(..))
import qualified Language.Haskell.Liquid.GHC.Misc  as GM -- (simplesymbol)
import qualified Data.HashMap.Strict               as M
import qualified Data.HashSet                      as S
-- import           Language.Fixpoint.Misc

import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types hiding     ( binds )

fixConfig :: FilePath -> Config -> FC.Config
fixConfig tgt cfg = FC.defConfig
  { FC.solver         = Mb.fromJust (smtsolver cfg)
  , FC.linear         = linear            cfg
  , FC.eliminate      = eliminate         cfg
  , FC.nonLinCuts     = not (higherOrderFlag cfg) -- eliminate cfg /= FC.All
  , FC.save           = saveQuery         cfg
  , FC.saveBfqOnError = saveBfqOnError    cfg
  , FC.srcFile        = tgt
  , FC.cores          = cores             cfg
  , FC.minPartSize    = minPartSize       cfg
  , FC.maxPartSize    = maxPartSize       cfg
  , FC.elimStats      = elimStats         cfg
  , FC.elimBound      = elimBound         cfg
  , FC.allowHO        = higherOrderFlag   cfg
  , FC.allowHOqs      = higherorderqs     cfg
  , FC.smtTimeout     = smtTimeout        cfg
  , FC.noStringTheory = not (stringTheory cfg)
  , FC.noslice        = noslice           cfg
  , FC.rewriteAxioms  = allowPLE   cfg
  , FC.pleUndecGuards = pleWithUndecidedGuards cfg
  , FC.etabeta        = etabeta    cfg
  , FC.localRewrites  = dependantCase cfg
  , FC.etaElim        = extensionality cfg
  , FC.extensionality = extensionality    cfg
  , FC.interpreter    = interpreter    cfg
  , FC.rwTermination  = rwTerminationCheck cfg
  , FC.fuel           = fuel      cfg
  , FC.noEnvReduction = not (environmentReduction cfg)
  , FC.inlineANFBinds = inlineANFBindings cfg
  }

cgInfoFInfo :: TargetInfo -> CGInfo -> IO (F.FInfo Cinfo)
cgInfoFInfo info cgi = return (targetFInfo info cgi)

targetFInfo :: TargetInfo -> CGInfo -> F.FInfo Cinfo
targetFInfo info cgi = mappend (mempty { F.ae = ax, F.lrws = localRewrites cgi }) fi
  where
    fi               = F.fi cs ws bs ls consts ks qs bi aHO aHOqs es mempty adts
    cs               = fixCs    cgi
    ws               = fixWfs   cgi
    bs               = binds    cgi
    ls               = fEnv     cgi
    consts           = cgConsts cgi
    ks               = kuts     cgi
    cfg              = getConfig info
    makeDecls        = adtFlag cfg
    adts             = if makeDecls then cgADTs   cgi else mempty
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
    eqs      = axioms
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
            let (Ghc.RealSrcSpan cc _) = ci_loc $ F.sinfo sub
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
canRewrite freeVars' from to = noFreeSyms && doesNotDiverge
  where
    fromSyms           = S.intersection freeVars' (F.syms from)
    toSyms             = S.intersection freeVars' (F.syms to)
    noFreeSyms         = S.null $ S.difference toSyms fromSyms
    doesNotDiverge     = Mb.isNothing (unify (S.toList freeVars') from to)
                      || Mb.isJust (unify (S.toList freeVars') to from)

refinementEQs :: LocSpecType -> [(F.Expr, F.Expr)]
refinementEQs t =
  case stripRTypeBase tres of
    Just r ->
      [ (lhs, rhs) | (F.EEq lhs rhs) <- F.splitPAnd $ F.reftPred (toReft r) ]
    Nothing ->
      []
  where
    tres = ty_res tRep
    tRep = toRTypeRep $ val t

makeRewriteOne :: F.TCEmb TyCon -> (Var, LocSpecType) -> [F.AutoRewrite]
makeRewriteOne tce (_, t)
  = [rw | (lhs, rhs) <- refinementEQs t , rw <- rewrites lhs rhs ]
  where

    rewrites :: F.Expr -> F.Expr -> [F.AutoRewrite]
    rewrites lhs rhs =
         (guard (canRewrite freeVars' lhs rhs) >> [F.AutoRewrite xs lhs rhs])
      ++ (guard (canRewrite freeVars' rhs lhs) >> [F.AutoRewrite xs rhs lhs])

    freeVars' = S.fromList (ty_binds tRep)

    xs = do
      (sym, arg) <- zip (ty_binds tRep) (ty_args tRep)
      let e = maybe F.PTrue (F.reftPred . toReft) (stripRTypeBase arg)
      return $ F.RR (RT.rTypeSort tce arg) (F.Reft (sym, e))

    tRep = toRTypeRep $ val t

_isClassOrDict :: Id -> Bool
_isClassOrDict x = F.tracepp ("isClassOrDict: " ++ F.showpp x) (hasClassArg x || GM.isDictionary x || Mb.isJust (Ghc.isClassOpId_maybe x))

hasClassArg :: Id -> Bool
hasClassArg x = F.tracepp msg (GM.isDataConId x && any Ghc.isClassPred (t:ts'))
  where
    msg       = "hasClassArg: " ++ showpp (x, t:ts')
    (ts, t)   = Ghc.splitFunTys . snd . Ghc.splitForAllTyCoVars . Ghc.varType $ x
    ts'       = map Ghc.irrelevantMult ts


doExpand :: TargetSpec -> Config -> F.SubC Cinfo -> Bool
doExpand sp cfg sub = allowGlobalPLE cfg
                   || (allowLocalPLE cfg && maybe False (isPLEVar sp) (subVar sub))

-- [TODO:missing-sorts] data-constructors often have unelaboratable 'define' so either
-- 1. Make `elaborate` robust so it doesn't crash and returns maybe or
-- 2. Make the `ctor` well-sorted or
-- 3. Don't create `define` for the ctor.
-- Unfortunately 3 breaks a bunch of tests...

-- Note [GADT workers and coercion binders]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- For GADT constructors, GHC generates a *worker* and a *wrapper* DataCon.
-- The worker's type includes coercion arguments for each equality constraint
-- (e.g. @Succ n ~ n+1@ for a length-indexed vector).  However, the fixpoint
-- SMT encoding drops those coercion arguments: a pattern match
-- @case xs of { (:>) x xr -> ... }@ produces a constraint
-- @xs = $:>(x, xr)@ with only the value arguments.
--
-- The spec type for the worker therefore has @nCoerce@ extra binders at the
-- front (one per equality constraint) that do NOT appear in the SMT
-- application.  We build the application expression using only the remaining
-- *value* binders (@valBs@), so that the resulting rewrite has the right
-- arity to fire on the worker applications that appear in constraints.
--
-- Note [All rewrites keyed on the worker symbol]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- In LiquidHaskell, @F.Symbolic DataCon@ is defined as
-- @symbol = F.symbol . dataConWorkId@, so DataCon applications in fixpoint
-- constraints *always* carry the *worker* symbol (e.g. @$:>@, never @$W:>@).
--
-- User-written measures (e.g. @vlen@) are routed to the *wrapper* spec type
-- by 'isWorkerDef' in "Measure", so @makeSimplify@ receives a
-- @(DataConWrapId $W:>, wrRType)@ pair carrying the measure refinements.
-- To produce rewrites that PLE can actually fire, we must key them on the
-- *worker* symbol rather than the wrapper symbol.  We do this by using
-- @dcSym = worker symbol@ in both the application expression @eVal@ and the
-- guard inside @go@, so the emitted 'F.SMeasure' entries are already
-- worker-keyed.

-- | Given @(dc, t)@ where @dc@ is a data constructor and @t@ is its spec type,
-- generate PLE rewrite rules for measures keyed on the worker DataCon symbol.
--
-- The measures are generated from the refinement in the result type of @t@,
-- which is expected to be of the form
--
-- > x0:t0 -> ... -> xn:tn -> { v: T | e }
--
-- where @e@ is a conjunction whose conjuncts have one of the following forms:
--
-- > f (dc x1 ... xn) = body
-- > f (dc x1 ... xn) <=> body
-- > f (dc x1 ... xn)
-- > not (f (dc x1 ... xn))
--
makeSimplify :: (Var, SpecType) -> [F.Rewrite]
makeSimplify (var, t)
  | not (GM.isDataConId var)
  = []
  | otherwise
  = go $ specTypeToResultRef eVal t
  where
    trep = toRTypeRep t
    -- All rewrites are keyed on the *worker* symbol.
    -- See note [All rewrites keyed on the worker symbol].
    dcSym = case Ghc.idDetails var of
      Ghc.DataConWrapId dc -> F.symbol (Ghc.dataConWorkId dc)
      _                    -> F.symbol var
    -- Value-only binders: for GADT workers, drop the leading coercion binders
    -- that are present in the spec type but absent in the SMT encoding.
    -- See note [GADT workers and coercion binders].
    valBs = case Ghc.idDetails var of
      Ghc.DataConWorkId dc ->
        let nCoerce = length $ filter (Ghc.isSimplePredTy . Ghc.irrelevantMult)
                              $ Ghc.dataConRepArgTys dc
        in  drop nCoerce (ty_binds trep)
      _                    -> ty_binds trep
    eVal  = F.eApps (F.EVar dcSym) (F.EVar <$> valBs)

    go (F.PAnd es) = concatMap go es

    go (F.PAtom eq (F.EApp (F.EVar f) expr) bd)
      | eq `elem` [F.Eq, F.Ueq]
      , (F.EVar dc, xs) <- F.splitEApp expr
      , dc == dcSym
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) bd]

    go (F.PIff (F.EApp (F.EVar f) expr) bd)
      | (F.EVar dc, xs) <- F.splitEApp expr
      , dc == dcSym
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) bd]

    go (F.EApp (F.EVar f) expr)
      | (F.EVar dc, xs) <- F.splitEApp expr
      , dc == dcSym
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) F.PTrue]

    go (F.PNot (F.EApp (F.EVar f) expr))
      | (F.EVar dc, xs) <- F.splitEApp expr
      , dc == dcSym
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) F.PFalse]

    go _ = []

    isEVar (F.EVar _) = True
    isEVar _ = False

    fromEVar (F.EVar x) = x
    fromEVar _ = impossible Nothing "makeSimplify.fromEVar"

specTypeToResultRef :: F.Expr -> SpecType -> F.Expr
specTypeToResultRef e t
  = mkExpr $ toReft $ Mb.fromMaybe mempty (stripRTypeBase $ ty_res trep)
  where
    mkExpr (F.Reft (v, ev)) = F.subst1 ev (v, e)
    trep                   = toRTypeRep t
