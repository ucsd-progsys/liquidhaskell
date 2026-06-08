{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE ImplicitParams            #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE TypeOperators             #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-record-selectors #-}

-- | This module defines the representation of Subtyping and WF Constraints,
--   and the code for syntax-directed constraint generation.

module Language.Haskell.Liquid.Constraint.Generate ( generateConstraints, caseEnv, consE ) where

import           Prelude                                       hiding (error)
import           GHC.Stack ( CallStack )
import           Liquid.GHC.API               as Ghc hiding ( panic
                                                            , (<+>)
                                                            , text
                                                            , vcat
                                                            )
import qualified Language.Haskell.Liquid.GHC.Resugar           as Rs
import qualified Language.Haskell.Liquid.GHC.SpanStack         as Sp
import qualified Language.Haskell.Liquid.GHC.Misc              as GM -- ( isInternal, collectArguments, tickSrcSpan, showPpr )
import Text.PrettyPrint.HughesPJ ( text )
import           Control.Monad ( foldM, forM, forM_, when, void, unless)
import           Control.Monad.State
import           Data.Bifunctor                                (first)
import           Data.Maybe                                    (fromMaybe, isJust, mapMaybe)
import           Data.Either.Extra                             (eitherToMaybe)
import qualified Data.HashMap.Strict                           as M
import qualified Data.HashSet                                  as S
import qualified Data.List                                     as L
import qualified Data.Foldable                                 as F
import qualified Data.Functor.Identity
import Language.Fixpoint.Misc (errorP, safeZip )
import           Language.Fixpoint.Types.Visitor
import qualified Language.Fixpoint.Types                       as F
import qualified Language.Fixpoint.Types.Visitor               as F
import           Language.Haskell.Liquid.Constraint.Fresh ( addKuts, freshTyType, trueTy )
import           Language.Haskell.Liquid.Constraint.Init ( initEnv, initCGI )
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Constraint.Monad
import Language.Haskell.Liquid.Constraint.Split ( splitC, splitW )
import           Language.Haskell.Liquid.Constraint.Relational (consAssmRel, consRelTop)
import           Language.Haskell.Liquid.Types.Dictionaries
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Fresh
import           Language.Haskell.Liquid.Types.Literals
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.PredType
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types hiding (binds)
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Constraint ( addConstraints )
import           Language.Haskell.Liquid.Constraint.Template
import           Language.Haskell.Liquid.Constraint.Termination
import           Language.Haskell.Liquid.Constraint.RewriteCase
import           Language.Haskell.Liquid.Transforms.CoreToLogic (weakenResult, runToLogic, coreToLogic)
import           Language.Haskell.Liquid.Bare.DataType (dataConMap, makeDataConChecker)
import Language.Haskell.Liquid.UX.Config
    ( HasConfig(getConfig),
      Config(typeclass, checkDerived, extensionality,
             nopolyinfer, dependantCase, rankNTypes, warnOnTermHoles),
      patternFlag,
      higherOrderFlag, warnOnTermHoles )
import qualified GHC.Data.Strict as Strict

-- Note [Term holes]
--
-- The term-hole implementation in this module is a small, opt-in pipeline that
-- is only active when @warnOnTermHoles@ is enabled.
--
-- The thesis motivating this feature chose constraint generation as the hook for
-- hole support because this is the first phase where LiquidHaskell already knows
-- the refined types and local environment that make a warning actionable. An
-- earlier location-based approach would have been more modular, but the needed
-- query from source locations back into constraint generation was not feasible.
--
-- The implementation also uses a stable hole naming convention, recognized by
-- 'isVarHole', instead of depending on GHC surface syntax alone. This keeps the
-- matching logic local to Core while reducing the amount of desugaring detail we
-- have to reconstruct.
--
-- 1. We detect direct occurrences of a typed hole with 'detectTypedHole', which
--    peels away ticks via 'stripTicks', recovers the hole source span with
--    'lastTick', and recognizes @hole@ binders with 'isVarHole'. We need this
--    normalization-aware detection because holes can appear under GHC-introduced
--    @App@ and @Tick@ nodes, and the warning should still point at the original
--    source span.
--
-- 2. We remember hole-shaped let-bindings in 'consCB''s local @checkLetHole@
--    helper. That helper records which ANF binder names a hole by calling
--    'linkANFToHole'. This step is needed because LiquidHaskell's ANF
--    normalization can float a hole into a fresh @let@ binder, and later useful
--    constraints may mention only that ANF name instead of the original hole.
--
-- 3. We record the type and environment of each direct hole occurrence while
--    generating constraints. In checking mode, 'cconsE''s local @maybeAddHole@
--    stores the expected type with 'addHole'. In synthesis mode, 'consE''s
--    local @synthesizeWithHole@ first synthesizes the application's type and
--    then stores that synthesized type with 'addHole'. We need both sites:
--    checking gives the expected type when one is available, while synthesis
--    covers cases like applications where checking alone would only report an
--    uninformative base type for the hole.
--
-- 4. We attach ANF expressions that participate in a hole by running
--    'checkANFHoleInExpr' from 'cconsE' and from the application case of
--    'consE'. That helper walks the expression with 'collectVars', resolves any
--    binder previously linked by 'linkANFToHole' through 'isANFInHole', and
--    saves the expression/type pair with 'addHoleANF'. This is what recovers the
--    surrounding refined constraints that users actually need when the hole sits
--    inside a larger normalized expression.
--
-- 5. After constraint generation finishes, 'consAct' calls
--    'emitConsolidatedHoleWarnings'. It merges the stored hole metadata with the
--    collected ANF expressions and emits one 'ErrHole' warning per hole, using
--    the environment captured by 'addHole' so the warning reports the local
--    typing context that was in scope at the hole. Delaying emission until the
--    end is important: only then do we have the direct hole information, the ANF
--    links, and the extra constraints together in one place.
--
-- Term holes were developed during the Master's thesis
--
-- Enhancing Proof Development in LiquidHaskell: Implementation and Evaluation of Typed Holes
-- MATHEUS DE SOUSA BERNARDO
-- Chalmers University of Technology, 2025
--
-- https://odr.chalmers.se/server/api/core/bitstreams/640ee29b-b13a-44d5-9e20-200a91a11021/content

--------------------------------------------------------------------------------
-- | Constraint Generation: Toplevel -------------------------------------------
--------------------------------------------------------------------------------
generateConstraints      :: TargetInfo -> CGInfo
--------------------------------------------------------------------------------
generateConstraints info = {-# SCC "ConsGen" #-} execState act $ initCGI cfg info
  where
    act                  = do { γ <- initEnv info; consAct γ cfg info }
    cfg                  = getConfig   info

consAct :: CGEnv -> Config -> TargetInfo -> CG ()
consAct γ cfg info = do
  let sSpc = gsSig . giSpec $ info
  let gSrc = giSrc info
  γ' <- foldM (consCBTop cfg info) γ (giCbs gSrc)
  -- Relational Checking: the following only runs when the list of relational specs is not empty
  (ψ, γ'') <- foldM (consAssmRel cfg info) ([], γ') (gsAsmRel sSpc ++ gsRelation sSpc)
  mapM_ (consRelTop cfg info γ'' ψ) (gsRelation sSpc)
  -- End: Relational Checking
  mapM_ (consClass γ) (gsMethods $ gsSig $ giSpec info)
  hcs <- gets hsCs
  hws <- gets hsWfs
  fcs <- concat <$> mapM (splitC (typeclass (getConfig info))) hcs
  fws <- concat <$> mapM splitW hws
  checkStratCtors γ sSpc
  when (warnOnTermHoles cfg) emitConsolidatedHoleWarnings
  modify $ \st -> st { fEnv     = fEnv    st `mappend` feEnv (fenv γ)
                     , cgLits   = litEnv   γ
                     , cgConsts = cgConsts st `mappend` constEnv γ
                     , fixCs    = fcs
                     , fixWfs   = fws }


---------------------------------
-- | Checking stratified ctors --
---------------------------------
type FExpr = F.ExprV F.Symbol
type Ctors = S.HashSet F.Symbol

checkStratCtors :: CGEnv -> GhcSpecSig -> CG ()
checkStratCtors env sSpc = do
  let ctors = S.fromList $ M.keys $ F.seBinds $ constEnv env
  let ctorRefinements = filter (isStrat . fst) $ gsTySigs sSpc
  forM_ ctorRefinements $ uncurry $ checkCtor ctors
  where
    -- (Alecs): For some reason it can't see that they are the same
    -- GHC name, probably is due to some worker wrapper shenannigans
    hack = occNameString . nameOccName
    isStrat nm = hack (varName nm) `elem` map hack (gsStratCtos sSpc)

uncurryPi :: SpecType -> ([SpecType], SpecType)
uncurryPi (RFun _ _ dom cod _) = first (dom :) $ uncurryPi cod
uncurryPi rest                 = ([], rest)

getTyConName :: SpecType -> Name
getTyConName a = Ghc.tyConName $ rtc_tc $ rt_tycon a

checkCtor :: Ctors -> Var -> LocSpecType -> CG ()
checkCtor ctors name typ = do
  let loc = GM.fSrcSpan $ F.loc typ
  let (args, ret) = uncurryPi $ val typ
  -- The constuctor that we want not to appear negatively
  let tyName = getTyConName ret
  -- Its index information
  retIdx <- case getPropIndex $ ur_reft $ rt_reft ret of
    Just idx -> pure idx
    Nothing  -> uError $ ErrStratNotPropRet loc (pprint tyName) (pprint name) (F.pprint ret)
  -- For every argument of the constructor we check that all the
  -- self-refernce are refined by a "smaller" `prop` annotation
  forM_ args $ checkNg ctors loc name tyName retIdx

checkNg :: Ctors -> SrcSpan -> Var -> Name -> FExpr -> SpecType -> CG ()
checkNg ctors loc ctorName tyName retIdx = go
  where
    go :: SpecType -> CG ()
    go RVar {} = pure ()
    go RAllT { rt_ty } = go rt_ty
    go RAllP { rt_ty } = go rt_ty
    go RFun { rt_in, rt_out } = do
      go rt_in
      go rt_out
    go r@RApp { rt_tycon = RTyCon { rtc_tc }, rt_args, rt_reft } = do
      if Ghc.tyConName rtc_tc == tyName then do
          case getPropIndex $ ur_reft rt_reft of
            (Just arg) -> do
              -- We compare index information The occurrence is safe
              -- iff the index of the return type is strictly bigger
              -- than the one in negative position
              unless (isStructurallySmaller ctors arg retIdx) $ do
                uError $ ErrStratIdxNotSmall loc
                  (pprint tyName) (pprint ctorName) (F.pprint retIdx) (F.pprint arg)
            -- We don't have index information for both so we bail
            _ -> uError $ ErrStratOccProp loc (pprint tyName) (pprint ctorName) (F.pprint r)
      else do
        forM_ rt_args go
    go _ = lift $ impossible (Just loc) "checkNg unexpected type"


isStructurallySmaller :: Ctors -> FExpr -> FExpr -> Bool
isStructurallySmaller ctors l r
  -- Congruence rule
  | (F.EVar nl, argsl) <- F.splitEAppThroughECst l
  , (F.EVar nr, argsr) <- F.splitEAppThroughECst r
  , nl == nr
  , length argsl == length argsr
  , nl `elem` ctors
  = lexOrder ctors argsl argsr
  | otherwise = isSubterm ctors l r && l /= r

lexOrder :: Ctors -> [F.ExprV F.Symbol] -> [F.ExprV F.Symbol] -> Bool
lexOrder _     []     []            = False
lexOrder ctors (l:ls) (r:rs)
  | isStructurallySmaller ctors l r = True
  | l == r                          = lexOrder ctors ls rs
  | otherwise                       = False
lexOrder _ _ _ = errorP "" "lexOrder: different length lists"

isSubterm :: Ctors -> FExpr -> FExpr -> Bool
isSubterm ctors l r | l == r
                   = True
                  -- Congruence rule
                  | (F.EVar nm, args) <- F.splitEAppThroughECst r
                  , nm `elem` ctors
                  = any (isSubterm ctors l) args
                  | otherwise
                  = False

-- | Emit one warning per recorded term hole after constraint generation has
--   collected both the hole metadata and any ANF expressions linked to it.
--
-- See Note [Term holes]
emitConsolidatedHoleWarnings :: CG ()
emitConsolidatedHoleWarnings = do
  holes     <- gets hsHoles
  holeExprs <- gets hsHolesExprs

  let mergedHoles
                  = [(h
                    , holeInfo
                    , M.findWithDefault [] (h, srcSpan) holeExprs
                    )
                    | ((h, srcSpan), holeInfo) <- M.toList holes
                    ]

  forM_ mergedHoles $ \(h, holeInfo, anfs) -> do
    let γ        = snd . info $ holeInfo
    let anfs'    = map (\(v, x, t) -> (F.symbol v, x, t)) anfs
    addWarning $ ErrHole (hloc holeInfo) "hole found" (reLocal $ renv γ) (F.symbol h) (htype holeInfo) anfs'


--------------------------------------------------------------------------------
-- | Ensure that the instance type is a subtype of the class type --------------
--------------------------------------------------------------------------------

consClass :: CGEnv -> (Var, MethodType LocSpecType) -> CG ()
consClass γ (x,mt)
  | Just ti <- tyInstance mt
  , Just tc <- tyClass    mt
  = addC (SubC (γ `setLocation` Sp.Span (GM.fSrcSpan (F.loc ti))) (F.tracepp ("consClass ti for " ++ GM.showPpr x) $ val ti) (F.tracepp ("consClass tc for " ++ GM.showPpr x) $ val tc)) ("cconsClass for " ++ GM.showPpr x)
consClass _ (_x, _mt)
  = return ()

--------------------------------------------------------------------------------
consCBLet :: CGEnv -> CoreBind -> CG CGEnv
--------------------------------------------------------------------------------
consCBLet γ cb = do
  oldtcheck <- gets tcheck
  isStr     <- doTermCheck (getConfig γ) cb
  -- TODO: yuck.
  modify $ \s -> s { tcheck = oldtcheck && isStr }
  γ' <- consCB (mkTCheck oldtcheck isStr) γ cb
  modify $ \s -> s{tcheck = oldtcheck}
  return γ'

--------------------------------------------------------------------------------
-- | Constraint Generation: Corebind -------------------------------------------
--------------------------------------------------------------------------------
consCBTop :: Config -> TargetInfo -> CGEnv -> CoreBind -> CG CGEnv
--------------------------------------------------------------------------------
consCBTop cfg info cgenv cb
  | all trustVar xs
  = foldM addB cgenv xs
    where
       xs   = bindersOf cb
       tt   = trueTy (typeclass cfg) . varType
       addB γ x = tt x >>= (\t -> γ += ("derived", F.symbol x, t))
       trustVar x = not (checkDerived cfg) && derivedVar (giSrc info) x

consCBTop _ _ γ cb
  = do oldtcheck <- gets tcheck
       -- lazyVars  <- specLazy <$> get
       isStr     <- doTermCheck (getConfig γ) cb
       modify $ \s -> s { tcheck = oldtcheck && isStr}
       -- remove invariants that came from the cb definition
       let (γ', i) = removeInvariant γ cb                 --- DIFF
       γ'' <- consCB (mkTCheck oldtcheck isStr) (γ'{cgVar = topBind cb}) cb
       modify $ \s -> s { tcheck = oldtcheck}
       return $ restoreInvariant γ'' i                    --- DIFF
    where
      topBind (NonRec v _)  = Just v
      topBind (Rec [(v,_)]) = Just v
      topBind _             = Nothing

--------------------------------------------------------------------------------
consCB :: TCheck -> CGEnv -> CoreBind -> CG CGEnv
--------------------------------------------------------------------------------
-- do termination checking
consCB TerminationCheck γ (Rec xes)
  = do texprs <- gets termExprs
       modify $ \i -> i { recCount = recCount i + length xes }
       let xxes = mapMaybe (`lookup'` texprs) xs
       if null xxes
         then consCBSizedTys consBind γ xes
         else check xxes <$> consCBWithExprs consBind γ xes
    where
      xs = map fst xes
      check ys r | length ys == length xs = r
                 | otherwise              = panic (Just loc) msg
      msg        = "Termination expressions must be provided for all mutually recursive binders"
      loc        = getSrcSpan (head xs)
      lookup' k m = (k,) <$> M.lookup k m

-- don't do termination checking, but some strata checks?
consCB StrataCheck γ (Rec xes)
  = do xets     <- forM xes $ \(x, e) -> (x, e,) <$> varTemplate γ (x, Just e)
       modify     $ \i -> i { recCount = recCount i + length xes }
       let xts    = [(x, to) | (x, _, to) <- xets]
       γ'        <- foldM extender (γ `setRecs` (fst <$> xts)) xts
       mapM_ (consBind True γ') xets
       return γ'

-- don't do termination checking, and don't do any strata checks either?
consCB NoCheck γ (Rec xes)
  = do xets   <- forM xes $ \(x, e) -> fmap (x, e,) (varTemplate γ (x, Just e))
       modify $ \i -> i { recCount = recCount i + length xes }
       let xts = [(x, to) | (x, _, to) <- xets]
       γ'     <- foldM extender (γ `setRecs` (fst <$> xts)) xts
       mapM_ (consBind True γ') xets
       return γ'

-- | NV: Dictionaries are not checked, because
-- | class methods' preconditions are not satisfied
consCB _ γ (NonRec x _) | isDictionary x
  = do t  <- trueTy (typeclass (getConfig γ)) (varType x)
       extender γ (x, Assumed t)
    where
       isDictionary = isJust . dlookup (denv γ)

consCB _ γ (NonRec x def)
  | Just (w, τ) <- grepDictionary def
  , Just d      <- dlookup (denv γ) w
  = do let τ' = F.tracepp ("dropInvisibleDictArgs " ++ GM.showPpr x ++ " w=" ++ GM.showPpr w ++ " nOrig=" ++ show (length τ) ++ " nFiltered=" ++ show (length (dropInvisibleDictArgs w τ))) $ dropInvisibleDictArgs w τ
       st       <- mapM (trueTy (typeclass (getConfig γ))) τ'
       mapM_ addW (WfC γ <$> st)
       let xts   = dmap (fmap (f st)) d
       let  γ'   = γ { denv = dinsert (denv γ) x xts }
       t        <- trueTy (typeclass (getConfig γ)) (varType x)
       extender γ' (x, Assumed t)
   where
    f [t']    (RAllT α te _) = subsTyVarMeet' (ty_var_value α, t') te
    f (t':ts) (RAllT α te _) = f ts $ subsTyVarMeet' (ty_var_value α, t') te
    f _ _ = impossible Nothing "consCB on Dictionary: this should not happen"

consCB _ γ (NonRec x e)
  = do to  <- varTemplate γ (x, Nothing)
       when (warnOnTermHoles (getConfig γ)) checkLetHole
       to' <- consBind False γ (x, e, to) >>= addPostTemplate γ
       extender γ (x, makeSingleton γ (simplify e) <$> to')
  where
    -- See Note [Term holes]
    checkLetHole =
      do
        let isItHole = detectTypedHole e
        case isItHole of
          Just (srcSpan, var) -> do
            linkANFToHole x (var, RealSrcSpan srcSpan Strict.Nothing)
          _ -> return ()
grepDictionary :: CoreExpr -> Maybe (Var, [Type])
grepDictionary = go []
  where
    go ts (App (Var w) (Type t)) = Just (w, reverse (t:ts))
    go ts (App e (Type t))       = go (t:ts) e
    go ts (App e (Var _))        = go ts e
    go ts (Let _ e)              = go ts e
    go _ _                       = Nothing

-- | Drop type arguments corresponding to invisible kind variables in the
-- dictionary function's type. In GHC 9.14+, poly-kinded instances have kind
-- variables that are Specified in the DFun but don't appear in LH specs.
-- We identify kind variables as those whose kind is exactly `Type` (they range
-- over types-as-kinds) AND whose name doesn't appear as a user-written variable.
-- Note: grepDictionary returns types in reversed application order, so we must
-- reverse before pairing with binders, then reverse back.
dropInvisibleDictArgs :: Var -> [Type] -> [Type]
dropInvisibleDictArgs w τs =
  let (bndrs, _) = Ghc.splitForAllForAllTyBinders (Ghc.varType w)
      -- Pair binders with types in forward (Core application) order
      forwardTypes = reverse τs
      filteredForward = go bndrs forwardTypes
  in reverse filteredForward
  where
    go (Ghc.Bndr v _ : bs) (t:ts)
      | isKindVar v = go bs ts       -- skip kind variable args
      | otherwise   = t : go bs ts   -- keep regular type variable args
    go _ ts = ts

    -- A kind variable is one whose kind is Type (TYPE (BoxedRep Lifted))
    -- These are introduced by kind generalization and don't appear in user specs.
    isKindVar v = Ghc.tyVarKind v `Ghc.eqType` Ghc.liftedTypeKind

--------------------------------------------------------------------------------
consBind :: Bool -> CGEnv -> (Var, CoreExpr, Template SpecType) -> CG (Template SpecType)
--------------------------------------------------------------------------------
consBind _ _ (x, _, Assumed t)
  | RecSelId {} <- idDetails x -- don't check record selectors with assumed specs
  = return $ F.notracepp ("TYPE FOR SELECTOR " ++ show x) $ Assumed t

consBind isRec' γ (x, e, Asserted spect)
  = do let γ'       = γ `setBind` x
           (_,πs,_) = bkUniv spect
       cgenv    <- foldM addPToEnv γ' πs
       cconsE cgenv e (weakenResult (typeclass (getConfig γ)) x spect)
       when (F.symbol x `elemHEnv` holes γ) $
         -- have to add the wf constraint here for HOLEs so we have the proper env
         addW $ WfC cgenv $ fmap killSubst spect
       addIdA x (defAnn isRec' spect)
       return $ Asserted spect

consBind isRec' γ (x, e, Internal spect)
  = do let γ'       = γ `setBind` x
           (_,πs,_) = bkUniv spect
       γπ    <- foldM addPToEnv γ' πs
       let γπ' = γπ {cerr = Just $ ErrHMeas (getLocation γπ) (pprint x) (text explanation)}
       cconsE γπ' e spect
       when (F.symbol x `elemHEnv` holes γ) $
         -- have to add the wf constraint here for HOLEs so we have the proper env
         addW $ WfC γπ $ fmap killSubst spect
       addIdA x (defAnn isRec' spect)
       return $ Internal spect
  where
    explanation = "Cannot give singleton type to the function definition."

consBind isRec' γ (x, e, Assumed spect)
  = do let γ' = γ `setBind` x
       γπ    <- foldM addPToEnv γ' πs
       cconsE γπ e =<< true (typeclass (getConfig γ)) spect
       addIdA x (defAnn isRec' spect)
       return $ Asserted spect
    where πs   = ty_preds $ toRTypeRep spect

consBind isRec' γ (x, e, Unknown)
  = do t'    <- consE (γ `setBind` x) e
       t     <- topSpecType x t'
       addIdA x (defAnn isRec' t)
       when (GM.isExternalId x) (addKuts x t)
       return $ Asserted t

killSubst :: RReft -> RReft
killSubst = mapReftField killSubstReft

killSubstReft :: F.Reft -> F.Reft
killSubstReft = trans ks
  where
    ks (F.PKVar k _ _) = F.PKVar k mempty mempty
    ks p                = p

-- | Add a type variable → sort mapping to every PKVar in a SpecType.
-- Used during type application to record how type variables are instantiated,
-- so the solver can apply the correct sort substitution to qualifier solutions.
addTyVarSubToKVars :: F.Symbol -> F.Sort -> SpecType -> SpecType
addTyVarSubToKVars sym sort = mapReft (mapReftField (trans addSub))
  where
    addSub (F.PKVar k tsu su) =
      let tsu' = M.map (F.applyCoercion sym sort) tsu
       in F.PKVar k (M.insert sym sort tsu') su
    addSub e                  = e

defAnn :: Bool -> t -> Annot t
defAnn True  = AnnRDf
defAnn False = AnnDef

addPToEnv :: CGEnv
          -> PVar RSort -> CG CGEnv
addPToEnv γ π
  = do γπ <- γ += ("addSpec1", pname π, pvarRType π)
       foldM (+=) γπ [("addSpec2", x, ofRSort t) | (t, x, _) <- pargs π]

-- | Detect a direct typed-hole occurrence in Core and recover the source span
--   that GHC attached to it, if present. The helper deliberately matches the
--   stable @.hole@ naming convention after stripping wrappers introduced by
--   desugaring and normalization.
--
-- See Note [Term holes]
detectTypedHole :: CoreExpr -> Maybe (RealSrcSpan, Var)
detectTypedHole e =
  case stripTicks e of
    Var x | isVarHole x ->
      case lastTick e of
        Just (SourceNote src _) -> Just (src, x)
        _                       -> Nothing
    _ -> Nothing

-- | Remove the outer application and tick wrappers that GHC places around a
--   hole so 'detectTypedHole' can inspect the underlying binder.
stripTicks :: CoreExpr -> CoreExpr
stripTicks (App (Tick _ e) _) = stripTicks e
stripTicks (Tick _ e)         = stripTicks e
stripTicks e          = e

-- | Traverse an expression and keep the innermost tick, which is the source
--   note used to report the hole location.
lastTick :: Expr b -> Maybe CoreTickish
lastTick (Tick t e) =
  case lastTick e of
    Just t' -> Just t'
    Nothing -> Just t
lastTick (App e a) =
  case lastTick a of
    Just ta -> Just ta
    Nothing -> lastTick e
lastTick _ = Nothing

-- | Check whether a Core binder name follows GHC's @.hole@ naming scheme for
--   typed holes.
isVarHole :: Var -> Bool
isVarHole x = isHoleStr (F.symbolString (F.symbol x))
  where
    isHoleStr s =
      case break (== '.') s of
        (_, '.':rest) -> rest == "hole"
        _             -> False

--------------------------------------------------------------------------------
-- | Bidirectional Constraint Generation: CHECKING -----------------------------
--------------------------------------------------------------------------------
cconsE :: CGEnv -> CoreExpr -> SpecType -> CG ()
--------------------------------------------------------------------------------
cconsE g e t = do
  checkANFHoleInExpr e t
  cconsE' g e t

--------------------------------------------------------------------------------
cconsE' :: CGEnv -> CoreExpr -> SpecType -> CG ()
--------------------------------------------------------------------------------
cconsE' γ e t
  | Just (Rs.PatSelfBind _x e') <- Rs.lift e
  = cconsE' γ e' t

  | Just (Rs.PatSelfRecBind x e') <- Rs.lift e
  = let γ' = γ { grtys = insertREnv (F.symbol x) t (grtys γ)}
    in void $ consCBLet γ' (Rec [(x, e')])

cconsE' γ e@(Let b@(NonRec x _) ee) t
  = do sp <- gets specLVars
       if x `S.member` sp
         then cconsLazyLet γ e t
         else do γ' <- consCBLet γ b
                 cconsE γ' ee t

cconsE' γ e (RAllP p t)
  = cconsE γ' e t''
  where
    t'         = replacePredsWithRefs su <$> t
    su         = (uPVar p, pVartoRConc p)
    (css, t'') = splitConstraints (typeclass (getConfig γ)) t'
    γ'         = L.foldl' addConstraints γ css

cconsE' γ (Let b e) t
  = do γ' <- consCBLet γ b
       cconsE γ' e t

cconsE' γ (Case e x _ cases) t
  = do γ' <- consCBLet γ (NonRec x e)
       forM_ cases $ cconsCase γ' x t nonDefAlts
    where
       nonDefAlts = [a | Alt a _ _ <- cases, a /= DEFAULT]
       _msg = "cconsE' #nonDefAlts = " ++ show (length nonDefAlts)

-- Skip invisible kind type lambdas that don't match the spec's forall.
-- GHC 9.14 introduces kind lambdas for poly-kinded instances.
-- Criterion: lambda has kind Type but the spec's forall variable has a different kind.
cconsE' γ (Lam α e) t@(RAllT α' _ _) | isTyVar α, isKindMismatch α α'
  = do γ' <- updateEnvironment γ α
       cconsE γ' e t

cconsE' γ (Lam α e) t | isTyVar α, isOrphanKindLambda α t
  = do γ' <- updateEnvironment γ α
       cconsE γ' e t

cconsE' γ (Lam α e) (RAllT α' t r) | isTyVar α
  = do γ' <- updateEnvironment γ α
       addForAllConstraint γ' α e (RAllT α' t r)
       cconsE γ' e $ subsTyVarMeet' (ty_var_value α', rVar α) t

cconsE' γ (Lam x e) (RFun y i ty t r)
  | not (isTyVar x)
  = do γ' <- γ += ("cconsE", x', ty)
       cconsE γ' e t'
       addFunctionConstraint γ x e (RFun x' i ty t' r')
       addIdA x (AnnDef ty)
  where
    x'  = F.symbol x
    t'  = t `F.subst1` (y, F.EVar x')
    r'  = r `F.subst1` (y, F.EVar x')

cconsE' γ (Tick tt e) t
  = cconsE (γ `setLocation` Sp.Tick tt) e t

cconsE' γ (Cast e co) t
  -- See Note [Type classes with a single method]
  | Just f <- isClassConCo co
  = cconsE γ (f e) t

cconsE' γ e@(Cast e' c) t
  = do t' <- (`strengthen` uTop (rTypeReft t)) <$> castTy γ (exprType e) e' c
       addC (SubC γ (F.notracepp ("Casted Type for " ++ GM.showPpr e ++ "\n init type " ++ showpp t) t') t) ("cconsE Cast: " ++ GM.showPpr e)

cconsE' γ e t
  = do
       when (warnOnTermHoles (getConfig γ))  maybeAddHole
       te  <- consE γ e
       te' <- instantiatePreds γ e te >>= addPost γ
       let te'' = propagateExpectedPreds te' t
       addC (SubC γ te'' t) ("cconsE: " ++ "\n t = " ++ showpp t ++ "\n te = " ++ showpp te ++ GM.showPpr e)
  where
    -- See Note [Term holes]
    -- Record the expected type of a direct hole encountered in checking mode.
    maybeAddHole = do
      let isItHole = detectTypedHole e
      case isItHole of
        Just (srcSpan, x) -> do
          addHole (RealSrcSpan srcSpan Strict.Nothing) x t γ
        _ -> return ()

-- | When the inferred type and expected type are both RApp of the same TyCon,
-- and the expected type has predicate arguments (abstract refinements), propagate
-- those predicates into the inferred type IF the inferred pred args are all
-- "unconstrained" (contain only KVars, not concrete predicates). This handles
-- phantom type parameters whose abstract predicates cannot be established through
-- data flow (e.g., TaggedT's user parameter).
propagateExpectedPreds :: SpecType -> SpecType -> SpecType
propagateExpectedPreds (RApp tc1 ts1 rs1 r1) (RApp tc2 _ts2 rs2 _r2)
  | rtc_tc tc1 == rtc_tc tc2
  , not (null rs2)
  , all isUnconstrainedPred rs1
  = RApp tc1 ts1 rs2 r1
propagateExpectedPreds te _t = te -- force rebuild

-- | A predicate arg is "unconstrained" if its inner type has only a KVar refinement
-- (from fresh type generation) or a trivial/empty refinement, NOT a concrete predicate.
isUnconstrainedPred :: SpecProp -> Bool
isUnconstrainedPred (RProp _ (RVar _ r)) = isKVarOrTrivial r
isUnconstrainedPred (RProp _ (RHole _))  = True
isUnconstrainedPred _                    = False

isKVarOrTrivial :: RReft -> Bool
isKVarOrTrivial r = isTauto r || hasOnlyKVars r

hasOnlyKVars :: RReft -> Bool
hasOnlyKVars (MkUReft (F.Reft (_, p)) _) = go p
  where
    go (F.PKVar _ _ _) = True
    go (F.PAnd ps)     = all go ps
    go F.PTrue         = True
    go _               = False

lambdaSingleton :: CGEnv -> F.TCEmb TyCon -> Var -> CoreExpr -> CG UReft
lambdaSingleton γ tce x e
  | higherOrderFlag γ
  = do expr <- lamExpr γ e
       return $ case expr of
         Just e' -> uTop $ F.exprReft $ F.ELam (F.symbol x, sx) e'
         _       -> mempty
  where
    sx = typeSort tce $ Ghc.expandTypeSynonyms $ varType x
lambdaSingleton _ _ _ _
  = return mempty

addForAllConstraint :: CGEnv -> Var -> CoreExpr -> SpecType -> CG ()
addForAllConstraint γ _ _ (RAllT rtv rt rr)
  | isTauto rr
  = return ()
  | otherwise
  = do t'       <- true (typeclass (getConfig γ)) rt
       let truet = RAllT rtv $ unRAllP t'
       addC (SubC γ (truet mempty) $ truet rr) "forall constraint true"
  where unRAllP (RAllT a t r) = RAllT a (unRAllP t) r
        unRAllP (RAllP _ t)   = unRAllP t
        unRAllP t             = t
addForAllConstraint γ _ _ _
  = impossible (Just $ getLocation γ) "addFunctionConstraint: called on non function argument"


addFunctionConstraint :: CGEnv -> Var -> CoreExpr -> SpecType -> CG ()
addFunctionConstraint γ x e (RFun y i ty t r)
  = do ty'      <- true (typeclass (getConfig γ)) ty
       t'       <- true (typeclass (getConfig γ)) t
       let truet = RFun y i ty' t'
       lamE <- lamExpr γ e
       case (lamE, higherOrderFlag γ) of
          (Just e', True) -> do tce    <- gets tyConEmbed
                                let sx  = typeSort tce $ varType x
                                let ref = uTop $ F.exprReft $ F.ELam (F.symbol x, sx) e'
                                addC (SubC γ (truet ref) $ truet r) "function constraint singleton"
          _ -> addC (SubC γ (truet mempty) $ truet r) "function constraint true"
addFunctionConstraint γ _ _ _
  = impossible (Just $ getLocation γ) "addFunctionConstraint: called on non function argument"

splitConstraints :: TyConable c
                 => Bool -> RType c tv r -> ([[(F.Symbol, RType c tv r)]], RType c tv r)
splitConstraints allowTC (RRTy cs _ OCons t)
  = let (css, t') = splitConstraints allowTC t in (cs:css, t')
splitConstraints allowTC (RFun x i tx@(RApp c _ _ _) t r) | isErasable c
  = let (css, t') = splitConstraints allowTC  t in (css, RFun x i tx t' r)
  where isErasable = if allowTC then isEmbeddedDict else isClass
splitConstraints _ t
  = ([], t)

-------------------------------------------------------------------
-- | @instantiatePreds@ peels away the universally quantified @PVars@
--   of a @RType@, generates fresh @Ref@ for them and substitutes them
--   in the body.
-------------------------------------------------------------------
instantiatePreds :: CGEnv
                 -> CoreExpr
                 -> SpecType
                 -> CG SpecType
instantiatePreds γ e (RAllP π t)
  = do r <- freshPredRef γ e π
       instantiatePreds γ e $ replacePreds "consE" t [(π, r)]

instantiatePreds _ _ t0
  = return t0


-------------------------------------------------------------------
cconsLazyLet :: CGEnv
             -> CoreExpr
             -> SpecType
             -> CG ()
cconsLazyLet γ (Let (NonRec x ex) e) t
  = do tx <- trueTy (typeclass (getConfig γ)) (varType x)
       γ' <- (γ, "Let NonRec") +++= (F.symbol x, ex, tx)
       cconsE γ' e t
cconsLazyLet _ _ _
  = panic Nothing "Constraint.Generate.cconsLazyLet called on invalid inputs"


---------------------------------------------------------
-- | Bidirectional Constraint Generation: SYNTHESIS ----------------------------
--------------------------------------------------------------------------------
consE :: CGEnv -> CoreExpr -> CG SpecType
--------------------------------------------------------------------------------
consE γ e
  | patternFlag γ
  , Just p <- Rs.lift e
  = consPattern γ (F.notracepp "CONSE-PATTERN: " p) (exprType e)

-- NV CHECK 3 (unVar and does this hack even needed?)
-- NV (below) is a hack to type polymorphic axiomatized functions
-- no need to check this code with flag, the axioms environment with
-- is empty if there is no axiomatization.

-- [NOTE: PLE-OPT] We *disable* refined instantiation for
-- reflected functions inside proofs.

-- If datacon definitions have references to self for fancy termination,
-- ignore them at the construction.
consE γ (Var x) | GM.isDataConId x
  = do t0 <- varRefType γ x
       -- NV: The check is expected to fail most times, so
       --     it is cheaper than direclty fmap ignoreSelf.
       let hasSelf = selfSymbol `S.member` F.syms t0
       let t = if hasSelf
                then mapReft (mapReftField ignoreSelf) t0
                else t0
       addLocA (Just x) (getLocation γ) (varAnn γ x t)
       return t

consE γ (Var x)
  = do t <- varRefType γ x
       addLocA (Just x) (getLocation γ) (varAnn γ x t)
       return t

consE _ (Lit c)
  = refreshVV $ uRType $ literalFRefType c

consE γ e'@(App _ _) =
  do
    t <- if warnOnTermHoles (getConfig γ) then synthesizeWithHole else consEApp γ e'
    checkANFHoleInExpr e' t
    return t
  where
    -- See Note [Term holes]
    -- Record the synthesized type of a direct hole encountered in synthesis
    -- mode before the caller consumes it.
    synthesizeWithHole = do
      let isItHole = detectTypedHole e'
      t <- consEApp γ e'
      _ <- case isItHole of
        Just (srcSpan, x) -> do
          addHole (RealSrcSpan srcSpan Strict.Nothing) x t γ
        _ -> return ()
      return t
consE γ (Lam α e) | isTyVar α
  = do γ' <- updateEnvironment γ α
       t' <- consE γ' e
       return $ RAllT (makeRTVar $ rTyVar α) t' mempty

consE γ  e@(Lam x e1)
  = do tx      <- freshTyType (typeclass (getConfig γ)) LamE (Var x) τx
       γ'      <- γ += ("consE", F.symbol x, tx)
       t1      <- consE γ' e1
       addIdA x $ AnnDef tx
       addW     $ WfC γ tx
       tce     <- gets tyConEmbed
       lamSing <- lambdaSingleton γ tce x e1
       return   $ RFun (F.symbol x) (mkRFInfo $ getConfig γ) tx t1 lamSing
    where
      FunTy { ft_arg = τx } = exprType e

consE γ e@(Let _ _)
  = cconsFreshE LetE γ e

consE γ e@(Case _ _ _ [_])
  | Just p@Rs.PatProject{} <- Rs.lift e
  = consPattern γ p (exprType e)

consE γ e@(Case _ _ _ cs)
  = cconsFreshE (caseKVKind cs) γ e

consE γ (Tick tt e)
  = do t <- consE (setLocation γ (Sp.Tick tt)) e
       addLocA Nothing (GM.tickSrcSpan tt) (AnnUse t)
       return t

-- See Note [Type classes with a single method]
consE γ (Cast e co)
  | Just f <- isClassConCo co
  = consE γ (f e)

consE γ e@(Cast e' c)
  = castTy γ (exprType e) e' c

consE γ e@(Coercion _)
   = trueTy (typeclass (getConfig γ)) $ exprType e

consE _ e@(Type t)
  = panic Nothing $ "consE cannot handle type " ++ GM.showPpr (e, t)

-- | Attach the current expression and inferred type to any ANF binders that
--   were previously recognized as naming a term hole. This compensates for ANF
--   normalization, which often moves the informative constraints from the hole
--   occurrence onto the fresh binder that stands for it.
--
-- See Note [Term holes]
checkANFHoleInExpr :: CoreExpr -> SpecType -> CG ()
checkANFHoleInExpr e t = do
  let vars = collectVars e
  forM_ vars $ \var -> do
    isANF <- isANFInHole var
    case isANF of
      Just uniqueVar -> addHoleANF uniqueVar var e t
      _ -> return ()
-- | Collect every variable mentioned in a Core expression so
--   'checkANFHoleInExpr' can look for ANF binders linked to a hole.
collectVars :: CoreExpr -> [Var]
collectVars (Var x) = [x]
collectVars (App e1 e2) = collectVars e1 ++ collectVars e2
collectVars (Lam x e) = x : collectVars e
collectVars (Let (NonRec x e1) e2) = x : collectVars e1 ++ collectVars e2
collectVars (Let (Rec xes) e) =
  let (xs, es) = unzip xes
  in xs ++ concatMap collectVars es ++ collectVars e
collectVars (Case e x _ alts) =
  x : collectVars e ++ concatMap collectAltVars alts
  where collectAltVars (Alt _ xs e') = xs ++ collectVars e'
collectVars _ = []

consEApp :: CGEnv -> CoreExpr -> CG SpecType
consEApp γ e'@(App e a@(Type τ))
  -- Skip invisible kind type applications (GHC Core has them but our SpecTypes don't)
  | isInvisibleTyApp e
  = consE γ e
  | otherwise
  = do
       RAllT α te _ <- checkAll ("Non-all TyApp with expr", e) γ <$> consE γ e
       t            <- if not (nopolyinfer (getConfig γ)) && isPos α && isGenericVar (ty_var_value α) te
                         then freshTyType (typeclass (getConfig γ)) TypeInstE e τ
                         else trueTy (typeclass (getConfig γ)) τ
       addW          $ WfC γ t
       t'           <- refreshVV t
       tt0          <- instantiatePreds γ e' (subsTyVarMeet' (ty_var_value α, t') te)
       let tyVarSym  = F.symbol (ty_var_value α)
           tyVarSort = typeSort (emb γ) (Ghc.expandTypeSynonyms τ)
           tt0'      = addTyVarSubToKVars tyVarSym tyVarSort tt0
           tt        = makeSingleton γ (simplify e') $ subsTyReft γ (ty_var_value α) τ tt0'
       return $ case rTVarToBind α of
         Just (x, _) -> maybe (checkUnbound γ e' x tt a) (F.subst1 tt . (x,)) (argType τ)
         Nothing     -> tt
  where
    isPos α = not (extensionality (getConfig γ)) || rtv_is_pol (ty_var_info α)

consEApp γ e'@(App e a) | Just aDict <- getExprDict γ a
  = case dhasinfo (dlookup (denv γ) aDict) (getExprFun γ e) of
      Just riSig -> do let t0 = F.tracepp ("DHASINFO t0 for " ++ GM.showPpr (getExprFun γ e)) $ fromRISig riSig
                           t  = F.tracepp ("DHASINFO stripped for " ++ GM.showPpr (getExprFun γ e)) $ stripMethodForalls e t0
                       return t
      _          -> do
        ([], πs, te) <- bkUniv <$> consE γ e
        te'          <- instantiatePreds γ e' $ foldr RAllP te πs
        (γ', te''')  <- dropExists γ te'
        te''         <- dropConstraints γ te'''
        updateLocA {- πs -} (exprLoc e) te''
        let RFun x _ tx t _ = checkFun ("Non-fun App with caller ", e') γ te''
        cconsE γ' a tx
        addPost γ'        $ maybe (checkUnbound γ' e' x t a) (F.subst1 t . (x,)) (argExpr γ a)

consEApp γ e'@(App e a)
  = do ([], πs, te) <- bkUniv <$> consE γ {- GM.tracePpr ("APP-EXPR: " ++ GM.showPpr (exprType e)) -} e
       te1        <- instantiatePreds γ e' $ foldr RAllP te πs
       (γ', te2)  <- dropExists γ te1
       te3        <- dropConstraints γ te2
       updateLocA (exprLoc e) te3
       let RFun x _ tx t _ = checkFun ("Non-fun App with caller ", e') γ te3
       cconsE γ' a tx
       makeSingleton γ' (simplify e') <$> addPost γ' (maybe (checkUnbound γ' e' x t a) (F.subst1 t . (x,)) (argExpr γ $ simplify a))
consEApp _ _ = panic Nothing "Constraint.Generate.consEApp called on invalid inputs"

-- | Check if a type application in GHC Core is for an invisible kind variable.
-- This happens when poly-kinded types have inferred/specified kind vars that
-- exist in Core but not in LH's SpecTypes.
-- We only skip Inferred foralls — Specified ones ARE tracked in SpecTypes.
isInvisibleTyApp :: CoreExpr -> Bool
isInvisibleTyApp e = case Ghc.splitForAllForAllTyBinders (Ghc.exprType e) of
  (Ghc.Bndr _ (Ghc.Invisible Ghc.InferredSpec) : _, _) -> True
  _ -> False

-- | Check if a Core type lambda is a kind variable that doesn't match
-- the spec's leading RAllT. This happens when the lambda binder has kind
-- Type (it's a kind variable) but the spec's forall variable has a
-- different kind (e.g., Type -> Type for a monad variable).
isKindMismatch :: Ghc.Var -> SpecRTVar -> Bool
isKindMismatch α α' =
  Ghc.tyVarKind α `Ghc.eqType` Ghc.liftedTypeKind &&
  case ty_var_value α' of
    RTV tv -> not (Ghc.tyVarKind tv `Ghc.eqType` Ghc.tyVarKind α)

-- | Check if a Core type lambda is an orphan kind variable (kind == Type)
-- that has no matching forall in the spec (spec type is not RAllT at all).
isOrphanKindLambda :: Ghc.Var -> SpecType -> Bool
isOrphanKindLambda α t =
  Ghc.tyVarKind α `Ghc.eqType` Ghc.liftedTypeKind && not (isRAllT t)
  where
    isRAllT (RAllT {}) = True
    isRAllT _          = False

-- | Strip leading foralls and class constraints from an instance method type
-- returned by dhasinfo. At the dict-application site, the class-level foralls
-- and class constraint have already been consumed (via the class selector type
-- app + dict application), so we strip them to get the method-level type.
-- Only strips if there IS a class constraint after the leading foralls.
stripMethodForalls :: CoreExpr -> SpecType -> SpecType
stripMethodForalls _e t
  | hasClassConstraint t = stripToMethod t
  | otherwise            = t
  where
    -- Check if there's a class constraint after leading foralls
    hasClassConstraint (RAllT _ ty _) = hasClassConstraint ty
    hasClassConstraint (RFun _ _ (RApp c _ _ _) _ _) = Ghc.isClassTyCon (rtc_tc c)
    hasClassConstraint _ = False
    -- Strip all leading RAllT foralls, then strip the class constraint RFun
    stripToMethod (RAllT _ ty _) = stripToMethod ty
    stripToMethod (RFun _ _ (RApp c _ _ _) body _)
      | Ghc.isClassTyCon (rtc_tc c) = body
    stripToMethod ty = ty

caseKVKind ::[Alt Var] -> KVKind
caseKVKind [Alt (DataAlt _) _ (Var _)] = ProjectE
caseKVKind cs                          = CaseE (length cs)

updateEnvironment :: CGEnv  -> TyVar -> CG CGEnv
updateEnvironment γ a
  | isValKind (tyVarKind a)
  = γ += ("varType", F.symbol $ varName a, kindToRType $ tyVarKind a)
  | otherwise
  = return γ

getExprFun :: CGEnv -> CoreExpr -> Var
getExprFun γ e          = go e
  where
    go (App x (Type _)) = go x
    go (Var x)          = x
    go _                = panic (Just (getLocation γ)) msg
    msg                 = "getFunName on \t" ++ GM.showPpr e

-- | `exprDict e` returns the dictionary `Var` inside the expression `e`
getExprDict :: CGEnv -> CoreExpr -> Maybe Var
getExprDict γ           =  go
  where
    go (Var x)          = case dlookup (denv γ) x of {Just _ -> Just x; Nothing -> Nothing}
    go (Tick _ e)       = go e
    go (App a (Type _)) = go a
    go (Let _ e)        = go e
    go _                = Nothing

--------------------------------------------------------------------------------
-- | With GADTs and reflection, refinements can contain type variables,
--   as 'coercions' (see ucsd-progsys/#1424). At application sites, we
--   must also substitute those from the refinements (not just the types).
--      https://github.com/ucsd-progsys/liquidhaskell/issues/1424
--
--   see: tests/ple/{pos,neg}/T1424.hs
--
--------------------------------------------------------------------------------

subsTyReft :: CGEnv -> RTyVar -> Type -> SpecType -> SpecType
subsTyReft γ a t = mapExprReft (\_ -> F.applyCoSub coSub)
  where
    coSub        = M.fromList [(F.symbol a, typeSort (emb γ) t)]

--------------------------------------------------------------------------------
-- | Type Synthesis for Special @Pattern@s -------------------------------------
--------------------------------------------------------------------------------
consPattern :: CGEnv -> Rs.Pattern -> Type -> CG SpecType

{- [NOTE] special type rule for monadic-bind application

    G |- e1 ~> m tx     G, x:tx |- e2 ~> m t
    -----------------------------------------
          G |- (e1 >>= \x -> e2) ~> m t
 -}

consPattern γ (Rs.PatBind e1 x e2 _ _ _ _ _) _ = do
  tx <- checkMonad (msg, e1) γ <$> consE γ e1
  γ' <- γ += ("consPattern", F.symbol x, tx)
  addIdA x (AnnDef tx)
  consE γ' e2
  where
    msg = "This expression has a refined monadic type; run with --no-pattern-inline: "

{- [NOTE] special type rule for monadic-return

           G |- e ~> et
    ------------------------
      G |- return e ~ m et
 -}
consPattern γ (Rs.PatReturn e m _ _ _) t = do
  et    <- F.notracepp "Cons-Pattern-Ret" <$> consE γ e
  mt    <- trueTy (typeclass (getConfig γ))  m
  tt    <- trueTy (typeclass (getConfig γ))  t
  return (mkRAppTy mt et tt) -- /// {-    $ RAppTy mt et mempty -}

{- [NOTE] special type rule for field projection, is
          t  = G(x)       ti = Proj(t, i)
    -----------------------------------------
      G |- case x of C [y1...yn] -> yi : ti
 -}

consPattern γ (Rs.PatProject xe _ τ c ys i) _ = do
  let yi = ys !! i
  t    <- freshTyType (typeclass (getConfig γ)) ProjectE (Var yi) τ
  _    <- (addW . WfC γ) t
  γ'   <- caseEnv γ xe [] (DataAlt c) ys (Just [i])
  ti   <- {- γ' ??= yi -} varRefType γ' yi
  addC (SubC γ' ti t) "consPattern:project"
  return t

consPattern γ (Rs.PatSelfBind _ e) _ =
  consE γ e

consPattern γ p@Rs.PatSelfRecBind{} _ =
  cconsFreshE LetE γ (Rs.lower p)

mkRAppTy :: SpecType -> SpecType -> SpecType -> SpecType
mkRAppTy mt et RAppTy{}          = RAppTy mt et mempty
mkRAppTy _  et (RApp c [_] [] _) = RApp c [et] [] mempty
mkRAppTy _  _  _                 = panic Nothing "Unexpected return-pattern"

checkMonad :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkMonad x g = go . unRRTy
 where
   go (RApp _ ts [] _)
     | not (null ts) = last ts
   go (RAppTy _ t _) = t
   go t              = checkErr x g t

unRRTy :: SpecType -> SpecType
unRRTy (RRTy _ _ _ t) = unRRTy t
unRRTy t              = t

--------------------------------------------------------------------------------
castTy  :: CGEnv -> Type -> CoreExpr -> Coercion -> CG SpecType
castTy' :: CGEnv -> Type -> CoreExpr -> CG SpecType
--------------------------------------------------------------------------------
castTy γ t e (AxiomCo ca _)
  = do
    msp <- case isNewtypeAxiomRule_maybe ca of
      Just (tc, _) -> lookupNewType tc
      _ -> return Nothing
    sp <- castTy' γ t e
    return (fromMaybe sp msp)

castTy γ t e (SymCo (AxiomCo ca _))
  = do mtc <- case isNewtypeAxiomRule_maybe ca of
         Just (tc, _) -> lookupNewType tc
         _ -> return Nothing
       F.forM_ mtc (cconsE γ e)
       castTy' γ t e

castTy γ t e _
  = castTy' γ t e


castTy' γ τ (Var x)
  = do t0 <- trueTy (typeclass (getConfig γ)) τ
       tx <- varRefType γ x
       let t = mergeCastTys t0 tx
       let ce = if typeclass (getConfig γ) then F.expr x
                  else eCoerc (typeSort (emb γ) $ Ghc.expandTypeSynonyms $ varType x)
                         (typeSort (emb γ) τ)
                         $ F.expr x
       return (t `strengthen` uTop (F.uexprReft ce) {- `meet` tx -})
  where eCoerc s t e
         | s == t    = e
         | otherwise = F.ECoerc s t e

castTy' γ t (Tick _ e)
  = castTy' γ t e

castTy' _ _ e
  = panic Nothing $ "castTy cannot handle expr " ++ GM.showPpr e


{-
mergeCastTys tcorrect trefined
  tcorrect has the correct GHC skeleton,
  trefined has the correct refinements (before coercion)
  mergeCastTys keeps the trefined when the two GHC types match
-}

mergeCastTys :: SpecType -> SpecType -> SpecType
mergeCastTys t1 t2
  | toType False t1 == toType False t2
  = t2
mergeCastTys (RApp c1 ts1 ps1 r1) (RApp c2 ts2 _ _)
  | c1 == c2
  = RApp c1 (zipWith mergeCastTys ts1 ts2) ps1 r1
mergeCastTys t _
  = t

{-
showCoercion :: Coercion -> String
showCoercion (AxiomInstCo co1 co2 co3)
  = "AxiomInstCo " ++ showPpr co1 ++ "\t\t " ++ showPpr co2 ++ "\t\t" ++ showPpr co3 ++ "\n\n" ++
    "COAxiom Tycon = "  ++ showPpr (coAxiomTyCon co1) ++ "\nBRANCHES\n" ++ concatMap showBranch bs
  where
    bs = fromBranchList $ co_ax_branches co1
    showBranch ab = "\nCoAxiom \nLHS = " ++ showPpr (coAxBranchLHS ab) ++
                    "\nRHS = " ++ showPpr (coAxBranchRHS ab)
showCoercion (SymCo c)
  = "Symc :: " ++ showCoercion c
showCoercion c
  = "Coercion " ++ showPpr c
-}

isClassConCo :: Coercion -> Maybe (Expr Var -> Expr Var)
-- See Note [Type classes with a single method]
isClassConCo co
  | Pair t1 t2 <- coercionKind co
  , isClassPred t2
  , (tc,ts) <- splitTyConApp t2
  , [dc]    <- tyConDataCons tc
  , [tm]    <- map irrelevantMult (Ghc.dataConOrigArgTys dc)
               -- tcMatchTy because we have to instantiate the class tyvars
  , Just _  <- ruleMatchTyX (mkUniqSet $ tyConTyVars tc) (mkRnEnv2 emptyInScopeSet) emptyTvSubstEnv tm t1
  = Just (\e -> mkCoreConApps dc $ map Type ts ++ [e])

  | otherwise
  = Nothing
  where
    ruleMatchTyX = ruleMatchTyKiX -- TODO: is this correct?

----------------------------------------------------------------------
-- Note [Type classes with a single method]
----------------------------------------------------------------------
-- GHC 7.10 encodes type classes with a single method as newtypes and
-- `cast`s between the method and class type instead of applying the
-- class constructor. Just rewrite the core to what we're used to
-- seeing..
--
-- specifically, we want to rewrite
--
--   e `cast` ((a -> b) ~ C)
--
-- to
--
--   D:C e
--
-- but only when
--
--   D:C :: (a -> b) -> C

--------------------------------------------------------------------------------
-- | @consFreshE@ is used to *synthesize* types with a **fresh template**.
--   e.g. at joins, recursive binders, polymorphic instantiations etc. It is
--   the "portal" that connects `consE` (synthesis) and `cconsE` (checking)
--------------------------------------------------------------------------------
cconsFreshE :: KVKind -> CGEnv -> CoreExpr -> CG SpecType
cconsFreshE kvkind γ e = do
  t   <- freshTyType (typeclass (getConfig γ)) kvkind e $ exprType e
  addW $ WfC γ t
  cconsE γ e t
  return t
--------------------------------------------------------------------------------

checkUnbound :: (PPrint a, Show a2, F.Subable a, F.Variable a ~ F.Symbol)
             => CGEnv -> CoreExpr -> F.Symbol -> a -> a2 -> a
checkUnbound γ e x t a
  | not (x `S.member` F.syms t) = t
  | otherwise            = panic (Just $ getLocation γ) msg
  where
    msg = unlines [ "checkUnbound: " ++ show x ++ " is elem of syms of " ++ showpp t
                  , "In"
                  , GM.showPpr e
                  , "Arg = "
                  , show a
                  ]

dropExists :: CGEnv -> SpecType -> CG (CGEnv, SpecType)
dropExists γ (REx x tx t) =         (, t) <$> γ += ("dropExists", x, tx)
dropExists γ t            = return (γ, t)

dropConstraints :: CGEnv -> SpecType -> CG SpecType
dropConstraints cgenv (RFun x i tx@(RApp c _ _ _) t r) | isErasable c
  = flip (RFun x i tx) r <$> dropConstraints cgenv t
  where
    isErasable = if typeclass (getConfig cgenv) then isEmbeddedDict else isClass
dropConstraints cgenv (RRTy cts _ OCons rt)
  = do γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("splitS", x,t)) cgenv xts
       addC (SubC γ' t1 t2)  "dropConstraints"
       dropConstraints cgenv rt
  where
    (xts, t1, t2) = envToSub cts

dropConstraints _ t = return t

-------------------------------------------------------------------------------------
cconsCase :: CGEnv -> Var -> SpecType -> [AltCon] -> CoreAlt -> CG ()
-------------------------------------------------------------------------------------
cconsCase γ x t acs (Alt ac ys ce)
  = do cγ <- caseEnv γ x acs ac ys mempty
       cconsE cγ ce t

{-

case x :: List b of
  Emp -> e

  Emp :: tdc          forall a. {v: List a | cons v === 0}
  x   :: xt           List b
  ys  == binders      []

-}
-------------------------------------------------------------------------------------
caseEnv   :: CGEnv -> Var -> [AltCon] -> AltCon -> [Var] -> Maybe [Int] -> CG CGEnv
-------------------------------------------------------------------------------------
caseEnv γ x _   (DataAlt c) ys pIs = do

  let (x' : ys')   = F.symbol <$> (x:ys)
  xt0             <- checkTyCon ("checkTycon cconsCase", x) γ <$> γ ??= x
  let rt           = shiftVV xt0 x'
  tdc             <- γ ??= dataConWorkId c >>= refreshVV
  let (rtd,yts',_) = unfoldR tdc rt ys
  yts             <- projectTypes (typeclass (getConfig γ))  pIs yts'
  let ys''         = F.symbol <$> filter (not . if allowTC then GM.isEmbeddedDictVar else GM.isEvVar) ys
  let r1           = dataConReft   c   ys''
  let r2           = dataConMsReft rtd ys''
  let xt           = (xt0 `meet` rtd) `strengthen` uTop (r1 `meet` r2)
  let cbs          = safeZip "cconsCase" (x':ys')
                         (map (`F.subst1` (selfSymbol, F.EVar x'))
                         (xt0 : yts))
  cγ'  <- addBinders γ   x' cbs
  when allowDC $
    addRewritesForNextBinding $ getCaseRewrites γ $ xt0 `meet` rtd
  addBinders cγ' x' [(x', substSelf <$> xt)]
  where allowTC    = typeclass (getConfig γ)
        allowDC    = dependantCase (getConfig γ)

caseEnv γ x acs a _ _ = do
  let x'  = F.symbol x
  xt'    <- (`strengthen` uTop (altReft γ acs a)) <$> (γ ??= x)
  addBinders γ x' [(x', xt')]


------------------------------------------------------
-- SELF special substitutions
------------------------------------------------------

substSelf :: UReft -> UReft
substSelf (MkUReft r p) = MkUReft (substSelfReft r) p

substSelfReft :: F.Reft -> F.Reft
substSelfReft (F.Reft (v, e)) = F.Reft (v, F.subst1 e (selfSymbol, F.EVar v))

ignoreSelf :: F.Reft -> F.Reft
ignoreSelf = F.mapExpr (\r -> if selfSymbol `S.member` F.syms r then F.PTrue else r)

--------------------------------------------------------------------------------
-- | `projectTypes` masks (i.e. true's out) all types EXCEPT those
--   at given indices; it is used to simplify the environment used
--   when projecting out fields of single-ctor datatypes.
--------------------------------------------------------------------------------
projectTypes :: Bool -> Maybe [Int] -> [SpecType] -> CG [SpecType]
projectTypes _        Nothing    ts = return ts
projectTypes allowTC (Just ints) ts = mapM (projT ints) (zip [0..] ts)
  where
    projT is (j, t)
      | j `elem` is = return t
      | otherwise   = true allowTC t

altReft :: CGEnv -> [AltCon] -> AltCon -> F.Reft
altReft _ _   (LitAlt l) = literalFReft l
altReft γ acs DEFAULT    = mconcat ([notLiteralReft l | LitAlt l <- acs] ++ [notDataConReft d | DataAlt d <- acs])
  where
    notLiteralReft   = maybe mempty F.notExprReft . snd . literalConst (emb γ)
    notDataConReft d = F.Reft (F.vv_, F.PNot (F.EApp (F.EVar $ makeDataConChecker d) (F.EVar F.vv_)))
altReft _ _ _            = panic Nothing "Constraint : altReft"

unfoldR :: SpecType -> SpecType -> [Var] -> (SpecType, [SpecType], SpecType)
unfoldR td (RApp _ ts rs _) ys = (t3, tvys ++ yts, ignoreOblig rt)
  where
        tbody                = instantiatePvs (instantiateTys td ts) (reverse rs)
        ((ys0,_,yts',_), rt) = safeBkArrow (F.notracepp msg $ instantiateTys tbody tvs')
        msg                  = "INST-TY: " ++ F.showpp (td, ts, tbody, ys, tvs')
        yts''                = zipWith F.subst sus (yts'++[rt])
        (t3,yts)             = (last yts'', init yts'')
        sus                  = F.mkSubst <$> L.inits [(x, F.EVar y) | (x, y) <- zip ys0 ys']
        (αs, ys')            = fmap F.symbol <$> L.partition isTyVar ys
        tvs' :: [SpecType]
        tvs'                 = rVar <$> αs
        tvys                 = ofType . varType <$> αs

unfoldR _  _                _  = panic Nothing "Constraint.hs : unfoldR"

instantiateTys :: SpecType -> [SpecType] -> SpecType
instantiateTys = L.foldl' go
  where
    go (RAllT α tbody _) t = subsTyVarMeet' (ty_var_value α, t) tbody
    go _ _                 = panic Nothing "Constraint.instantiateTy"

instantiatePvs :: SpecType -> [SpecProp] -> SpecType
instantiatePvs           = L.foldl' go
  where
    go (RAllP p tbody) r = replacePreds "instantiatePv" tbody [(p, r)]
    go t               _ = errorP "" ("Constraint.instantiatePvs: t = " ++ showpp t)

checkTyCon :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkTyCon _ _ t@RApp{} = t
checkTyCon x g t        = checkErr x g t

checkFun :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkFun _ _ t@RFun{} = t
checkFun x g t        = checkErr x g t

checkAll :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkAll _ _ t@RAllT{} = t
checkAll x g t         = checkErr x g t

checkErr :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkErr (msg, e) γ t = panic (Just sp) $ msg ++ GM.showPpr e ++ ", type: " ++ showpp t
  where
    sp                = getLocation γ

varAnn :: CGEnv -> Var -> t -> Annot t
varAnn γ x t
  | x `S.member` recs γ = AnnLoc (getSrcSpan x)
  | otherwise           = AnnUse t

-----------------------------------------------------------------------
-- | Helpers: Creating Fresh Refinement -------------------------------
-----------------------------------------------------------------------
freshPredRef :: CGEnv -> CoreExpr -> PVar RSort -> CG SpecProp
freshPredRef γ e (PV _ rsort as)
  = do t    <- freshTyType (typeclass (getConfig γ))  PredInstE e (toType False rsort)
       args <- mapM (const fresh) as
       let targs = [(x, s) | (x, (s, y, z)) <- zip args as, F.EVar y == z ]
       γ' <- foldM (+=) γ [("freshPredRef", x, ofRSort τ) | (x, τ) <- targs]
       addW $ WfC γ' t
       return $ RProp targs t

--------------------------------------------------------------------------------
-- | Helpers: Creating Refinement Types For Various Things ---------------------
--------------------------------------------------------------------------------
argType :: Type -> Maybe F.Expr
argType (LitTy (NumTyLit i)) = mkI i
argType (LitTy (StrTyLit s)) = Just $ mkS $ bytesFS s
argType (TyVarTy x)          = Just $ F.EVar $ F.symbol $ varName x
argType t
  | F.symbol (GM.showPpr t) == anyTypeSymbol
                             = Just $ F.EVar anyTypeSymbol
argType _                    = Nothing


argExpr :: CGEnv -> CoreExpr -> Maybe F.Expr
argExpr _ (Var v)          = Just $ F.eVar v
argExpr γ (Lit c)          = snd $ literalConst (emb γ) c
argExpr γ (Tick _ e)       = argExpr γ e
argExpr γ (App e (Type _)) = argExpr γ e
argExpr _ _                = Nothing


lamExpr :: CGEnv -> CoreExpr -> CG (Maybe F.Expr)
lamExpr g e = do
    adts <- gets cgADTs
    let dm = dataConMap adts
    return $ eitherToMaybe $ runToLogic (emb g) mempty dm (getConfig g)
      (\x -> todo Nothing ("coreToLogic not working lamExpr: " ++ x))
      (coreToLogic e)

--------------------------------------------------------------------------------
(??=) :: (?callStack :: CallStack) => CGEnv -> Var -> CG SpecType
--------------------------------------------------------------------------------
γ ??= x = case M.lookup x' (lcb γ) of
            Just e  -> consE (γ -= x') e
            Nothing -> refreshTy tx
          where
            x' = F.symbol x
            tx = fromMaybe tt (γ ?= x')
            tt = ofType $ varType x


--------------------------------------------------------------------------------
varRefType :: (?callStack :: CallStack) => CGEnv -> Var -> CG SpecType
--------------------------------------------------------------------------------
varRefType γ x =
  varRefType' γ x <$> (γ ??= x) -- F.tracepp (printf "varRefType x = [%s]" (showpp x))

varRefType' :: CGEnv -> Var -> SpecType -> SpecType
varRefType' γ x t'
  | Just tys <- trec γ, Just tr  <- M.lookup x' tys
  = strengthen' tr xr
  | otherwise
  = strengthen' t' xr
  where
    xr = singletonReft x
    x' = F.symbol x
    strengthen' | higherOrderFlag γ = strengthenMeet
                | otherwise         = strengthenTop

-- | create singleton types for function application
makeSingleton :: CGEnv -> CoreExpr -> SpecType -> SpecType
makeSingleton γ cexpr t
  | higherOrderFlag γ, App f x <- simplify cexpr
  = case (funExpr γ f, argForAllExpr x) of
      (Just f', Just x')
                 | not (if typeclass (getConfig γ) then GM.isEmbeddedDictExpr x else GM.isPredExpr x) -- (isClassPred $ exprType x)
                 -> strengthenMeet t (uTop $ F.exprReft (F.EApp f' x'))
      (Just f', Just _)
                 -> strengthenMeet t (uTop $ F.exprReft f')
      _ -> t
  | rankNTypes (getConfig γ)
  = case argExpr γ (simplify cexpr) of
       Just e' -> strengthenMeet t $ uTop (F.exprReft e')
       _       -> t
  | otherwise
  = t
  where
    argForAllExpr (Var x)
      | rankNTypes (getConfig γ)
      , Just e <- M.lookup x (forallcb γ)
      = Just e
    argForAllExpr e
      = argExpr γ e



funExpr :: CGEnv -> CoreExpr -> Maybe F.Expr

funExpr _ (Var v)
  = Just $ F.EVar (F.symbol v)

funExpr γ (App e1 e2)
  = case (funExpr γ e1, argExpr γ e2) of
      (Just e1', Just e2') | not (if typeclass (getConfig γ) then GM.isEmbeddedDictExpr e2
                                                             else GM.isPredExpr e2) -- (isClassPred $ exprType e2)
                           -> Just (F.EApp e1' e2')
      (Just e1', Just _)   -> Just e1'
      _                    -> Nothing

funExpr _ _
  = Nothing

simplify :: CoreExpr -> CoreExpr
simplify (Tick _ e)            = simplify e
simplify (App e (Type _))      = simplify e
simplify (App e1 e2)           = App (simplify e1) (simplify e2)
simplify (Lam x e) | isTyVar x = simplify e
simplify e                     = e


singletonReft :: (F.Symbolic a) => a -> UReft
singletonReft = uTop . F.symbolReft . F.symbol

-- | RJ: `nomeet` replaces `strengthenS` for `strengthen` in the definition
--   of `varRefType`. Why does `tests/neg/strata.hs` fail EVEN if I just replace
--   the `otherwise` case? The fq file holds no answers, both are sat.
strengthenTop :: (PPrint r, Meet r) => RType c tv r -> r -> RType c tv r
strengthenTop (RApp c ts rs r) r'   = RApp c ts rs   $ meet r r'
strengthenTop (RVar a r) r'         = RVar a         $ meet r r'
strengthenTop (RFun b i t1 t2 r) r' = RFun b i t1 t2 $ meet r r'
strengthenTop (RAppTy t1 t2 r) r'   = RAppTy t1 t2   $ meet r r'
strengthenTop (RAllT a t r)    r'   = RAllT a t      $ meet r r'
strengthenTop t _                   = t

-- TODO: this is almost identical to RT.strengthen! merge them!
strengthenMeet :: (PPrint r, Meet r) => RType c tv r -> r -> RType c tv r
strengthenMeet (RApp c ts rs r) r'  = RApp c ts rs (r `meet` r')
strengthenMeet (RVar a r) r'        = RVar a       (r `meet` r')
strengthenMeet (RFun b i t1 t2 r) r'= RFun b i t1 t2 (r `meet` r')
strengthenMeet (RAppTy t1 t2 r) r'  = RAppTy t1 t2 (r `meet` r')
strengthenMeet (RAllT a t r) r'     = RAllT a (strengthenMeet t r') (r `meet` r')
strengthenMeet t _                  = t

--------------------------------------------------------------------------------
-- | Cleaner Signatures For Rec-bindings ---------------------------------------
--------------------------------------------------------------------------------
exprLoc                         :: CoreExpr -> Maybe SrcSpan
exprLoc (Tick tt _)             = Just $ GM.tickSrcSpan tt
exprLoc (App e a) | isType a    = exprLoc e
exprLoc _                       = Nothing

isType :: Expr CoreBndr -> Bool
isType (Type _)                 = True
isType a                        = eqType (exprType a) predType

-- | @isGenericVar@ determines whether the @RTyVar@ has no class constraints
isGenericVar :: RTyVar -> SpecType -> Bool
isGenericVar α st =  all (\(c, α') -> (α'/=α) || isGenericClass c ) (classConstrs st)
  where
    classConstrs t = [(c, ty_var_value α')
                        | (c, ts) <- tyClasses t
                        , t'      <- ts
                        , α'      <- freeTyVars t']
    isGenericClass c = className c `elem` [ordClassName, eqClassName] -- , functorClassName, monadClassName]

-- instance MonadFail CG where
--  fail msg = panic Nothing msg

instance MonadFail Data.Functor.Identity.Identity where
  fail msg = panic Nothing msg
