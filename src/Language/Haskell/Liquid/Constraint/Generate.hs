{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams            #-}

-- | This module defines the representation of Subtyping and WF Constraints,
--   and the code for syntax-directed constraint generation.

module Language.Haskell.Liquid.Constraint.Generate ( generateConstraints ) where

import           Outputable                                    (Outputable)
import           Prelude                                       hiding (error)
import           GHC.Stack
import           CoreUtils                                     (exprType)
import           MkCore
import           Coercion
import           DataCon
import           Pair
import           CoreSyn
import           SrcLoc                                 hiding (Located)
import           Type
import           VarEnv (mkRnEnv2, emptyInScopeSet)
import           TyCon
import           CoAxiom
import           PrelNames
import           Language.Haskell.Liquid.GHC.TypeRep
import           Class                                         (className)
import           Var
import           IdInfo
import           Name        hiding (varName)
import           FastString (fastStringToByteString)
import           Unify
import           UniqSet (mkUniqSet)
import           Text.PrettyPrint.HughesPJ hiding ((<>)) 
import           Control.Monad.State
import           Control.Monad.Fail 
import           Data.Maybe                                    (fromMaybe, catMaybes, isJust)
import qualified Data.HashMap.Strict                           as M
import qualified Data.HashSet                                  as S
import qualified Data.List                                     as L
import qualified Data.Foldable                                 as F
import qualified Data.Traversable                              as T
import qualified Data.Functor.Identity
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types.Visitor
import qualified Language.Fixpoint.Types                       as F
import qualified Language.Fixpoint.Types.Visitor               as F
-- import           Language.Fixpoint.Solver.Instantiate
import           Language.Haskell.Liquid.Constraint.Fresh
import           Language.Haskell.Liquid.Constraint.Init
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Constraint.Monad
import           Language.Haskell.Liquid.Constraint.Split
import           Language.Haskell.Liquid.Types.Dictionaries
import           Language.Haskell.Liquid.GHC.Play          (isHoleVar) 
import qualified Language.Haskell.Liquid.GHC.Resugar           as Rs
import qualified Language.Haskell.Liquid.GHC.SpanStack         as Sp
import           Language.Haskell.Liquid.Types                 hiding (binds, Loc, loc, Def)
import           Language.Haskell.Liquid.Types.Names       (anyTypeSymbol)
-- import           Language.Haskell.Liquid.Types.Strata
-- import qualified Language.Haskell.Liquid.Types.RefType         as RT
-- import           Language.Haskell.Liquid.Types.PredType        hiding (freeTyVars)
-- import           Language.Haskell.Liquid.Types.Literals
import qualified Language.Haskell.Liquid.GHC.Misc         as GM -- ( isInternal, collectArguments, tickSrcSpan, showPpr )
import           Language.Haskell.Liquid.Misc
-- NOPROVER import           Language.Haskell.Liquid.Constraint.Axioms
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Constraint
import           Language.Haskell.Liquid.Transforms.Rec
import           Language.Haskell.Liquid.Transforms.CoreToLogic (weakenResult)
import           Language.Haskell.Liquid.Bare.DataType (makeDataConChecker)

--------------------------------------------------------------------------------
-- | Constraint Generation: Toplevel -------------------------------------------
--------------------------------------------------------------------------------
generateConstraints      :: GhcInfo -> CGInfo
--------------------------------------------------------------------------------
generateConstraints info = {-# SCC "ConsGen" #-} execState act $ initCGI cfg info
  where
    act                  = consAct cfg info
    cfg                  = getConfig   info

consAct :: Config -> GhcInfo -> CG ()
consAct cfg info = do
  γ       <- initEnv      info
  sflag   <- scheck   <$> get
  let sSpc = gsSig . giSpec $ info  
  let gSrc = giSrc info
  when (gradual cfg) (mapM_ (addW . WfC γ . val . snd) (gsTySigs sSpc ++ gsAsmSigs sSpc))
  foldM_ (consCBTop cfg info) γ (giCbs gSrc)
  mapM (consClass γ) (gsMethods $ gsSig $ giSpec info) 
  hcs    <- hsCs  <$> get
  hws    <- hsWfs <$> get
  scss   <- sCs   <$> get
  annot  <- annotMap <$> get
  scs    <- if sflag then concat <$> mapM splitS (hcs ++ scss)
                    else return []
  let smap = if sflag then solveStrata scs else []
  let hcs' = if sflag then subsS smap hcs else hcs
  fcs <- concat <$> mapM splitC (subsS smap hcs')
  fws <- concat <$> mapM splitW hws
  let annot' = if sflag then subsS smap <$> annot else annot
  modify $ \st -> st { fEnv     = feEnv (fenv γ)
                     , cgLits   = litEnv   γ
                     , cgConsts = (cgConsts st) `mappend` (constEnv γ)
                     , fixCs    = fcs
                     , fixWfs   = fws
                     , annotMap = annot' }



--------------------------------------------------------------------------------
-- | Ensure that the instance type is a subtype of the class type --------------
--------------------------------------------------------------------------------

consClass :: CGEnv -> (Var, MethodType LocSpecType) -> CG ()
consClass γ (x,mt) 
  | Just ti <- tyInstance mt 
  , Just tc <- tyClass    mt 
  = addC (SubC (γ `setLocation` Sp.Span (GM.fSrcSpan (F.loc ti))) (val ti) (val tc)) ("cconsClass for " ++ GM.showPpr x)
consClass _ _ 
  = return () 

--------------------------------------------------------------------------------
-- | TERMINATION TYPE ----------------------------------------------------------
--------------------------------------------------------------------------------
makeDecrIndex :: (Var, Template SpecType, [Var]) -> CG [Int]
makeDecrIndex (x, Assumed t, args)
  = do dindex <- makeDecrIndexTy x t args
       case dindex of
         Left _  -> return []
         Right i -> return i
makeDecrIndex (x, Asserted t, args)
  = do dindex <- makeDecrIndexTy x t args
       case dindex of
         Left msg -> addWarning msg >> return []
         Right i  -> return i
makeDecrIndex _ = return []

makeDecrIndexTy :: Var -> SpecType -> [Var] -> CG (Either (TError t) [Int])
makeDecrIndexTy x t args
  = do spDecr <- specDecr <$> get
       autosz <- autoSize <$> get
       hint   <- checkHint' autosz (L.lookup x spDecr)
       case dindex autosz of
         Nothing -> return $ Left msg
         Just i  -> return $ Right $ fromMaybe [i] hint
    where
       ts         = ty_args trep
       tvs        = zip ts args
       checkHint' = \autosz -> checkHint x ts (isDecreasing autosz cenv)
       dindex     = \autosz -> L.findIndex (p autosz) tvs
       p autosz (t, v) = isDecreasing autosz cenv t && not (isIdTRecBound v)
       msg        = ErrTermin (getSrcSpan x) [F.pprint x] (text "No decreasing parameter")
       cenv       = makeNumEnv ts
       trep       = toRTypeRep $ unOCons t


recType :: F.Symbolic a
        => S.HashSet TyCon
        -> (([a], [Int]), (t, [Int], SpecType))
        -> SpecType
recType _ ((_, []), (_, [], t))
  = t

recType autoenv ((vs, indexc), (_, index, t))
  = makeRecType autoenv t v dxt index
  where v    = (vs !!)  <$> indexc
        dxt  = (xts !!) <$> index
        xts  = zip (ty_binds trep) (ty_args trep)
        trep = toRTypeRep $ unOCons t

checkIndex :: (NamedThing t, PPrint t, PPrint [a])
           => (t, [a], Template (RType c tv r), [Int])
           -> CG [Maybe (RType c tv r)]
checkIndex (x, vs, t, index)
  = do mapM_ (safeLogIndex msg1 vs) index
       mapM  (safeLogIndex msg2 ts) index
    where
       loc   = getSrcSpan x
       ts    = ty_args $ toRTypeRep $ unOCons $ unTemplate t
       msg1  = ErrTermin loc [xd] ("No decreasing" <+> F.pprint index <-> "-th argument on" <+> xd <+> "with" <+> (F.pprint vs))
       msg2  = ErrTermin loc [xd] "No decreasing parameter"
       xd    = F.pprint x

makeRecType :: (Enum a1, Eq a1, Num a1, F.Symbolic a)
            => S.HashSet TyCon
            -> SpecType
            -> [a]
            -> [(F.Symbol, SpecType)]
            -> [a1]
            -> SpecType
makeRecType autoenv t vs dxs is
  = mergecondition t $ fromRTypeRep $ trep {ty_binds = xs', ty_args = ts'}
  where
    (xs', ts') = unzip $ replaceN (last is) (makeDecrType autoenv vdxs) xts
    vdxs       = zip vs dxs
    xts        = zip (ty_binds trep) (ty_args trep)
    trep       = toRTypeRep $ unOCons t

unOCons :: RType c tv r -> RType c tv r
unOCons (RAllT v t)        = RAllT v $ unOCons t
unOCons (RAllP p t)        = RAllP p $ unOCons t
unOCons (RFun x tx t r)    = RFun x (unOCons tx) (unOCons t) r
unOCons (RRTy _ _ OCons t) = unOCons t
unOCons t                  = t

mergecondition :: RType c tv r -> RType c tv r -> RType c tv r
mergecondition (RAllT _ t1) (RAllT v t2)               = RAllT v (mergecondition t1 t2)
mergecondition (RAllP _ t1) (RAllP p t2)               = RAllP p (mergecondition t1 t2)
mergecondition (RRTy xts r OCons t1) t2                = RRTy xts r OCons (mergecondition t1 t2)
mergecondition (RFun _ t11 t12 _) (RFun x2 t21 t22 r2) = RFun x2 (mergecondition t11 t21) (mergecondition t12 t22) r2
mergecondition _ t                                     = t

safeLogIndex :: Error -> [a] -> Int -> CG (Maybe a)
safeLogIndex err ls n
  | n >= length ls = addWarning err >> return Nothing
  | otherwise      = return $ Just $ ls !! n

checkHint :: (NamedThing a, PPrint a, PPrint [a1])
          => a -> [a1] -> (a1 -> Bool) -> Maybe [Int] -> CG (Maybe [Int])
checkHint _ _ _ Nothing
  = return Nothing

checkHint x _ _ (Just ns) | L.sort ns /= ns
  = addWarning (ErrTermin loc [dx] (text "The hints should be increasing")) >> return Nothing
  where
    loc = getSrcSpan x
    dx  = F.pprint x

checkHint x ts f (Just ns)
  = (mapM (checkValidHint x ts f) ns) >>= (return . Just . catMaybes)

checkValidHint :: (NamedThing a, PPrint a, PPrint [a1])
               => a -> [a1] -> (a1 -> Bool) -> Int -> CG (Maybe Int)
checkValidHint x ts f n
  | n < 0 || n >= length ts = addWarning err >> return Nothing
  | f (ts L.!! n)           = return $ Just n
  | otherwise               = addWarning err >> return Nothing
  where
    err = ErrTermin loc [xd] (vcat [ "Invalid Hint" <+> F.pprint (n+1) <+> "for" <+> xd
                                   , "in"
                                   , F.pprint ts ])
    loc = getSrcSpan x
    xd  = F.pprint x

--------------------------------------------------------------------------------
consCBLet :: CGEnv -> CoreBind -> CG CGEnv
--------------------------------------------------------------------------------
consCBLet γ cb = do
  oldtcheck <- tcheck <$> get
  isStr     <- doTermCheck (getConfig γ) cb
  -- TODO: yuck.
  modify $ \s -> s { tcheck = oldtcheck && isStr }
  γ' <- consCB (oldtcheck && isStr) isStr γ cb
  modify $ \s -> s{tcheck = oldtcheck}
  return γ'

--------------------------------------------------------------------------------
-- | Constraint Generation: Corebind -------------------------------------------
--------------------------------------------------------------------------------
consCBTop :: Config -> GhcInfo -> CGEnv -> CoreBind -> CG CGEnv
--------------------------------------------------------------------------------
consCBTop cfg info γ cb
  | all (trustVar cfg info) xs
  = foldM addB γ xs
    where
       xs   = bindersOf cb
       tt   = trueTy . varType
       addB γ x = tt x >>= (\t -> γ += ("derived", F.symbol x, t))

consCBTop _ _ γ cb
  = do oldtcheck <- tcheck <$> get
       -- lazyVars  <- specLazy <$> get
       isStr     <- doTermCheck (getConfig γ) cb
       modify $ \s -> s { tcheck = oldtcheck && isStr}
       -- remove invariants that came from the cb definition
       let (γ', i) = removeInvariant γ cb                 --- DIFF
       γ'' <- consCB (oldtcheck && isStr) isStr (γ'{cgVar = topBind cb}) cb
       modify $ \s -> s { tcheck = oldtcheck}
       return $ restoreInvariant γ'' i                    --- DIFF
    where
      topBind (NonRec v _)  = Just v
      topBind (Rec [(v,_)]) = Just v
      topBind _             = Nothing

trustVar :: Config -> GhcInfo -> Var -> Bool
trustVar cfg info x = not (checkDerived cfg) && derivedVar (giSrc info) x

derivedVar :: GhcSrc -> Var -> Bool
derivedVar src x = S.member x (giDerVars src)

doTermCheck :: Config -> Bind Var -> CG Bool
doTermCheck cfg bind = do 
  lazyVs    <- specLazy   <$> get 
  termVs    <- specTmVars <$> get
  let skip   = any (\x -> S.member x lazyVs || GM.isInternal x) xs
  let chk    = not (structuralTerm cfg) || any (\x -> S.member x termVs) xs
  return     $ chk && not skip
  where 
    xs       = bindersOf bind

-- nonStructTerm && not skip

-- RJ: AAAAAAARGHHH!!!!!! THIS CODE IS HORRIBLE!!!!!!!!!
consCBSizedTys :: CGEnv -> [(Var, CoreExpr)] -> CG CGEnv
consCBSizedTys γ xes
  = do xets''    <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       sflag     <- scheck <$> get
       autoenv   <- autoSize <$> get
       let cmakeFinType = if sflag then makeFinType else id
       let cmakeFinTy   = if sflag then makeFinTy   else snd
       let xets = mapThd3 (fmap cmakeFinType) <$> xets''
       ts'      <- mapM (T.mapM refreshArgs) $ (thd3 <$> xets)
       let vs    = zipWith collectArgs ts' es
       is       <- mapM makeDecrIndex (zip3 xs ts' vs) >>= checkSameLens
       let ts = cmakeFinTy  <$> zip is ts'
       let xeets = (\vis -> [(vis, x) | x <- zip3 xs is $ map unTemplate ts]) <$> (zip vs is)
       (L.transpose <$> mapM checkIndex (zip4 xs vs ts is)) >>= checkEqTypes
       let rts   = (recType autoenv <$>) <$> xeets
       let xts   = zip xs ts
       γ'       <- foldM extender γ xts
       let γs    = zipWith makeRecInvariants [γ' `setTRec` zip xs rts' | rts' <- rts] (filter (not . GM.isPredVar) <$> vs)
       let xets' = zip3 xs es ts
       mapM_ (uncurry $ consBind True) (zip γs xets')
       return γ'
  where
       (xs, es)       = unzip xes
       dxs            = F.pprint <$> xs
       collectArgs    = GM.collectArguments . length . ty_binds . toRTypeRep . unOCons . unTemplate
       checkEqTypes :: [[Maybe SpecType]] -> CG [[SpecType]]
       checkEqTypes x = mapM (checkAll err1 toRSort) (catMaybes <$> x)
       checkSameLens  = checkAll err2 length
       err1           = ErrTermin loc dxs $ text "The decreasing parameters should be of same type"
       err2           = ErrTermin loc dxs $ text "All Recursive functions should have the same number of decreasing parameters"
       loc            = getSrcSpan (head xs)

       checkAll _   _ []            = return []
       checkAll err f (x:xs)
         | all (==(f x)) (f <$> xs) = return (x:xs)
         | otherwise                = addWarning err >> return []

consCBWithExprs :: CGEnv -> [(Var, CoreExpr)] -> CG CGEnv
consCBWithExprs γ xes
  = do xets'     <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       texprs    <- termExprs <$> get
       let xtes   = catMaybes $ (`lookup` texprs) <$> xs
       sflag     <- scheck <$> get
       let cmakeFinType = if sflag then makeFinType else id
       let xets  = mapThd3 (fmap cmakeFinType) <$> xets'
       let ts    = safeFromAsserted err . thd3 <$> xets
       ts'      <- mapM refreshArgs ts
       let xts   = zip xs (Asserted <$> ts')
       γ'       <- foldM extender γ xts
       let γs    = makeTermEnvs γ' xtes xes ts ts'
       let xets' = zip3 xs es (Asserted <$> ts')
       mapM_ (uncurry $ consBind True) (zip γs xets')
       return γ'
  where (xs, es) = unzip xes
        lookup k m | Just x <- M.lookup k m = Just (k, x)
                   | otherwise              = Nothing
        err      = "Constant: consCBWithExprs"

makeFinTy :: (Eq a, Functor f, Num a, Foldable t)
          => (t a, f SpecType)
          -> f SpecType
makeFinTy (ns, t) = fmap go t
  where
    go t = fromRTypeRep $ trep {ty_args = args'}
      where
        trep = toRTypeRep t
        args' = mapNs ns makeFinType $ ty_args trep

makeTermEnvs :: CGEnv -> [(Var, [F.Located F.Expr])] -> [(Var, CoreExpr)]
             -> [SpecType] -> [SpecType]
             -> [CGEnv]
makeTermEnvs γ xtes xes ts ts' = setTRec γ . zip xs <$> rts
  where
    vs   = zipWith collectArgs ts es
    ys   = (fst4 . bkArrowDeep) <$> ts
    ys'  = (fst4 . bkArrowDeep) <$> ts'
    sus' = zipWith mkSub ys ys'
    sus  = zipWith mkSub ys ((F.symbol <$>) <$> vs)
    ess  = (\x -> (safeFromJust (err x) $ (x `L.lookup` xtes))) <$> xs
    tes  = zipWith (\su es -> F.subst su <$> es)  sus ess
    tes' = zipWith (\su es -> F.subst su <$> es)  sus' ess
    rss  = zipWith makeLexRefa tes' <$> (repeat <$> tes)
    rts  = zipWith (addObligation OTerm) ts' <$> rss
    (xs, es)     = unzip xes
    mkSub ys ys' = F.mkSubst [(x, F.EVar y) | (x, y) <- zip ys ys']
    collectArgs  = GM.collectArguments . length . ty_binds . toRTypeRep
    err x        = "Constant: makeTermEnvs: no terminating expression for " ++ GM.showPpr x

addObligation :: Oblig -> SpecType -> RReft -> SpecType
addObligation o t r  = mkArrow αs πs ls yts xts $ RRTy [] r o t2
  where
    (αs, πs, ls, t1) = bkUniv t
    ((xs',ts',rs'),(xs, ts, rs), t2) = bkArrow t1
    xts              = zip3 xs ts rs
    yts              = zip3 xs' ts' rs'

--------------------------------------------------------------------------------
consCB :: Bool -> Bool -> CGEnv -> CoreBind -> CG CGEnv
--------------------------------------------------------------------------------
-- do termination checking
consCB True _ γ (Rec xes)
  = do texprs <- termExprs <$> get
       modify $ \i -> i { recCount = recCount i + length xes }
       let xxes = catMaybes $ (`lookup` texprs) <$> xs
       if null xxes
         then consCBSizedTys γ xes
         else check xxes <$> consCBWithExprs γ xes
    where
      xs = fst (unzip xes)
      check ys r | length ys == length xs = r
                 | otherwise              = panic (Just loc) $ msg
      msg        = "Termination expressions must be provided for all mutually recursive binders"
      loc        = getSrcSpan (head xs)
      lookup k m = (k,) <$> M.lookup k m

-- don't do termination checking, but some strata checks?
consCB _ False γ (Rec xes)
  = do xets'     <- forM xes $ \(x, e) -> (x, e,) <$> varTemplate γ (x, Just e)
       sflag     <- scheck <$> get
       let mkDivT = if sflag then makeDivType else id
       let xets   = mapThd3 (fmap mkDivT) <$> xets'
       modify     $ \i -> i { recCount = recCount i + length xes }
       let xts    = [(x, to) | (x, _, to) <- xets]
       γ'        <- foldM extender (γ `setRecs` (fst <$> xts)) xts
       mapM_ (consBind True γ') xets
       return γ'

-- don't do termination checking, and don't do any strata checks either?
consCB _ _ γ (Rec xes)
  = do xets   <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       modify $ \i -> i { recCount = recCount i + length xes }
       let xts = [(x, to) | (x, _, to) <- xets]
       γ'     <- foldM extender (γ `setRecs` (fst <$> xts)) xts
       mapM_ (consBind True γ') xets
       return γ'

-- | NV: Dictionaries are not checked, because
-- | class methods' preconditions are not satisfied
consCB _ _ γ (NonRec x _) | isDictionary x
  = do t  <- trueTy (varType x)
       extender γ (x, Assumed t)
    where
       isDictionary = isJust . dlookup (denv γ)


consCB _ _ γ (NonRec x def)
  | Just (w, τ) <- grepDictionary def
  , Just d      <- dlookup (denv γ) w
  = do t        <- trueTy τ
       addW      $ WfC γ t
       let xts   = dmap (fmap (f t)) d
       let  γ'   = γ { denv = dinsert (denv γ) x xts }
       t        <- trueTy (varType x)
       extender γ' (x, Assumed t)
   where
    f t' (RAllT α te) = subsTyVar_meet' (ty_var_value α, t') te
    f _ _ = impossible Nothing "consCB on Dictionary: this should not happen"

consCB _ _ γ (NonRec x e)
  = do to  <- varTemplate γ (x, Nothing)
       to' <- consBind False γ (x, e, to) >>= (addPostTemplate γ)
       extender (addRankNBind γ x e) (x, to')

grepDictionary :: CoreExpr -> Maybe (Var, Type)
grepDictionary (App (Var w) (Type t)) = Just (w, t)
grepDictionary (App e (Var _))        = grepDictionary e
grepDictionary _                      = Nothing

--------------------------------------------------------------------------------
consBind :: Bool -> CGEnv -> (Var, CoreExpr, Template SpecType) -> CG (Template SpecType)
--------------------------------------------------------------------------------
consBind _ _ (x, _, Assumed t)
  | RecSelId {} <- idDetails x -- don't check record selectors with assumed specs
  = return $ F.notracepp ("TYPE FOR SELECTOR " ++ show x) $ Assumed t

consBind isRec γ (x, e, Asserted spect)
  = do let γ'         = γ `setBind` x
           (_,πs,_,_) = bkUniv spect
       γπ    <- foldM addPToEnv γ' πs

       -- take implcits out of the function's SpecType and into the env
       let tyr = toRTypeRep spect
       let spect' = fromRTypeRep (tyr { ty_ebinds = [], ty_eargs = [], ty_erefts = [] })
       γπ <- foldM (+=) γπ $ (\(y,t)->("implicitError",y,t)) <$> zip (ty_ebinds tyr) (ty_eargs tyr)

       cconsE γπ e (weakenResult x spect')
       when (F.symbol x `elemHEnv` holes γ) $
         -- have to add the wf constraint here for HOLEs so we have the proper env
         addW $ WfC γπ $ fmap killSubst spect
       addIdA x (defAnn isRec spect)
       return $ Asserted spect

consBind isRec γ (x, e, Internal spect)
  = do let γ'         = γ `setBind` x
           (_,πs,_,_) = bkUniv spect
       γπ    <- foldM addPToEnv γ' πs
       let γπ' = γπ {cerr = Just $ ErrHMeas (getLocation γπ) (pprint x) (text explanation)}
       cconsE γπ' e spect
       when (F.symbol x `elemHEnv` holes γ) $
         -- have to add the wf constraint here for HOLEs so we have the proper env
         addW $ WfC γπ $ fmap killSubst spect
       addIdA x (defAnn isRec spect)
       return $ Internal spect
  where
    explanation = "Cannot give singleton type to the function definition."

consBind isRec γ (x, e, Assumed spect)
  = do let γ' = γ `setBind` x
       γπ    <- foldM addPToEnv γ' πs
       cconsE γπ e =<< true spect
       addIdA x (defAnn isRec spect)
       return $ Asserted spect
    where πs   = ty_preds $ toRTypeRep spect

consBind isRec γ (x, e, Unknown)
  = do t'    <- consE (γ `setBind` x) e
       t     <- topSpecType x t'
       addIdA x (defAnn isRec t)
       when (isExportedId x) (addKuts x t)
       return $ Asserted t

killSubst :: RReft -> RReft
killSubst = fmap killSubstReft

killSubstReft :: F.Reft -> F.Reft
killSubstReft = trans kv () ()
  where
    kv    = defaultVisitor { txExpr = ks }
    ks _ (F.PKVar k _) = F.PKVar k mempty
    ks _ p             = p

defAnn :: Bool -> t -> Annot t
defAnn True  = AnnRDf
defAnn False = AnnDef

addPToEnv :: CGEnv
          -> PVar RSort -> CG CGEnv
addPToEnv γ π
  = do γπ <- γ += ("addSpec1", pname π, pvarRType π)
       foldM (+=) γπ [("addSpec2", x, ofRSort t) | (t, x, _) <- pargs π]

extender :: F.Symbolic a => CGEnv -> (a, Template SpecType) -> CG CGEnv
extender γ (x, Asserted t)
  = case lookupREnv (F.symbol x) (assms γ) of
      Just t' -> γ += ("extender", F.symbol x, t')
      _       -> γ += ("extender", F.symbol x, t)
extender γ (x, Assumed t)
  = γ += ("extender", F.symbol x, t)
extender γ _
  = return γ

data Template a
  = Asserted a
  | Assumed a
  | Internal a
  | Unknown
  deriving (Functor, F.Foldable, T.Traversable)

deriving instance (Show a) => (Show (Template a))

instance PPrint a => PPrint (Template a) where
  pprintTidy k (Asserted t) = "Asserted" <+> pprintTidy k t
  pprintTidy k (Assumed  t) = "Assumed"  <+> pprintTidy k t
  pprintTidy k (Internal t) = "Internal" <+> pprintTidy k t
  pprintTidy _ Unknown      = "Unknown"

unTemplate :: Template t -> t
unTemplate (Asserted t) = t
unTemplate (Assumed t)  = t
unTemplate (Internal t) = t
unTemplate _            = panic Nothing "Constraint.Generate.unTemplate called on `Unknown`"

addPostTemplate :: CGEnv
                -> Template SpecType
                -> CG (Template SpecType)
addPostTemplate γ (Asserted t) = Asserted <$> addPost γ t
addPostTemplate γ (Assumed  t) = Assumed  <$> addPost γ t
addPostTemplate γ (Internal t) = Internal  <$> addPost γ t
addPostTemplate _ Unknown      = return Unknown

safeFromAsserted :: [Char] -> Template t -> t
safeFromAsserted _ (Asserted t) = t
safeFromAsserted msg _ = panic Nothing $ "safeFromAsserted:" ++ msg

-- | @varTemplate@ is only called with a `Just e` argument when the `e`
-- corresponds to the body of a @Rec@ binder.
varTemplate :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Template SpecType)
varTemplate γ (x, eo) = varTemplate' γ (x, eo) >>= mapM (topSpecType x)

-- | @lazVarTemplate@ is like `varTemplate` but for binders that are *not*
--   termination checked and hence, the top-level refinement / KVar is
--   stripped out. e.g. see tests/neg/T743.hs
-- varTemplate :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Template SpecType)
-- lazyVarTemplate γ (x, eo) = dbg <$> (topRTypeBase <$>) <$> varTemplate' γ (x, eo)
--   where
--    dbg   = traceShow ("LAZYVAR-TEMPLATE: " ++ show x)

varTemplate' :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Template SpecType)
varTemplate' γ (x, eo)
  = case (eo, lookupREnv (F.symbol x) (grtys γ), lookupREnv (F.symbol x) (assms γ), lookupREnv (F.symbol x) (intys γ)) of
      (_, Just t, _, _) -> Asserted <$> refreshArgsTop (x, t)
      (_, _, _, Just t) -> Internal <$> refreshArgsTop (x, t)
      (_, _, Just t, _) -> Assumed  <$> refreshArgsTop (x, t)
      (Just e, _, _, _) -> do t  <- freshTy_expr (RecBindE x) e (exprType e)
                              addW (WfC γ t)
                              Asserted <$> refreshArgsTop (x, t)
      (_,      _, _, _) -> return Unknown

-- | @topSpecType@ strips out the top-level refinement of "derived var"
topSpecType :: Var -> SpecType -> CG SpecType
topSpecType x t = do
  info  <- ghcI <$> get
  return $ if derivedVar (giSrc info) x then topRTypeBase t else t

--------------------------------------------------------------------------------
-- | Bidirectional Constraint Generation: CHECKING -----------------------------
--------------------------------------------------------------------------------
cconsE :: CGEnv -> CoreExpr -> SpecType -> CG ()
--------------------------------------------------------------------------------
cconsE g e t = do
  -- NOTE: tracing goes here
  -- traceM $ printf "cconsE:\n  expr = %s\n  exprType = %s\n  lqType = %s\n" (showPpr e) (showPpr (exprType e)) (showpp t)
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
  = do sp <- specLVars <$> get
       if (x `S.member` sp)
         then cconsLazyLet γ e t
         else do γ'  <- consCBLet γ b
                 cconsE γ' ee t

cconsE' γ e (RAllP p t)
  = cconsE γ' e t''
  where
    t'         = replacePredsWithRefs su <$> t
    su         = (uPVar p, pVartoRConc p)
    (css, t'') = splitConstraints t'
    γ'         = L.foldl' addConstraints γ css

cconsE' γ (Let b e) t
  = do γ'  <- consCBLet γ b
       cconsE γ' e t

cconsE' γ (Case e x _ cases) t
  = do γ'  <- consCBLet γ (NonRec x e)
       forM_ cases $ cconsCase (addArgument γ' x) x t nonDefAlts
    where
       nonDefAlts = [a | (a, _, _) <- cases, a /= DEFAULT]
       _msg = "cconsE' #nonDefAlts = " ++ show (length (nonDefAlts))

cconsE' γ (Lam α e) (RAllT α' t) | isTyVar α
  = do γ' <- updateEnvironment γ α
       cconsE γ' e $ subsTyVar_meet' (ty_var_value α', rVar α) t

cconsE' γ (Lam x e) (RFun y ty t r)
  | not (isTyVar x)
  = do γ' <- γ += ("cconsE", x', ty)
       cconsE (addArgument γ' x) e t'
       addFunctionConstraint (addArgument γ x) x e (RFun x' ty t' r')
       addIdA x (AnnDef ty)
  where
    x'  = F.symbol x
    t'  = t `F.subst1` (y, F.EVar x')
    r'  = r `F.subst1` (y, F.EVar x')

cconsE' γ (Tick tt e) t
  = cconsE (γ `setLocation` (Sp.Tick tt)) e t

cconsE' γ (Cast e co) t
  -- See Note [Type classes with a single method]
  | Just f <- isClassConCo co
  = cconsE γ (f e) t

cconsE' γ e@(Cast e' c) t
  = do t' <- castTy γ (exprType e) e' c
       addC (SubC γ t' t) ("cconsE Cast: " ++ GM.showPpr e)

cconsE' γ (Var x) t | isHoleVar x && typedHoles (getConfig γ)
  = addHole x t γ 

cconsE' γ e t
  = do te  <- consE γ e
       te' <- instantiatePreds γ e te >>= addPost γ
       addC (SubC γ te' t) ("cconsE: " ++ GM.showPpr e)

lambdaSingleton :: CGEnv -> F.TCEmb TyCon -> Var -> CoreExpr -> UReft F.Reft
lambdaSingleton γ tce x e
  | higherOrderFlag γ, Just e' <- lamExpr γ e
  = uTop $ F.exprReft $ F.ELam (F.symbol x, sx) e'
  where
    sx = typeSort tce $ varType x
lambdaSingleton _ _ _ _
  = mempty


addFunctionConstraint :: CGEnv -> Var -> CoreExpr -> SpecType -> CG ()
addFunctionConstraint γ x e (RFun y ty t r)
  = do ty'      <- true ty
       t'       <- true t
       let truet = RFun y ty' t'
       case (lamExpr γ e, higherOrderFlag γ) of
          (Just e', True) -> do tce    <- tyConEmbed <$> get
                                let sx  = typeSort tce $ varType x
                                let ref = uTop $ F.exprReft $ F.ELam (F.symbol x, sx) e'
                                addC (SubC γ (truet ref) $ truet r)    "function constraint singleton"
          _ -> addC (SubC γ (truet mempty) $ truet r) "function constraint true"
addFunctionConstraint γ _ _ _
  = impossible (Just $ getLocation γ) "addFunctionConstraint: called on non function argument"

splitConstraints :: TyConable c
                 => RType c tv r -> ([[(F.Symbol, RType c tv r)]], RType c tv r)
splitConstraints (RRTy cs _ OCons t)
  = let (css, t') = splitConstraints t in (cs:css, t')
splitConstraints (RFun x tx@(RApp c _ _ _) t r) | isClass c
  = let (css, t') = splitConstraints t in (css, RFun x tx t' r)
splitConstraints t
  = ([], t)

-------------------------------------------------------------------
-- | @instantiateGhosts@ peels away implicit argument binders,
-- instantiates them with fresh variables, and adds those variables
-- to the context as @ebind@s TODO: the second half
-------------------------------------------------------------------
instantiateGhosts :: CGEnv
                 -> SpecType
                 -> CG (Bool, CGEnv, SpecType)
instantiateGhosts γ t | not (null yts)
  = do ys' <- mapM (const fresh) ys
       γ'  <- foldM addEEnv γ (zip ys' ts)

       let su = F.mkSubst $ zip ys (F.EVar <$> ys')
       return (True, γ', F.subst su te')
  where (yts, te') = bkImplicit t
        (ys, ts)   = unzip yts

instantiateGhosts γ t = return (False, γ, t)

bkImplicit :: RType c tv r
           -> ( [(F.Symbol, RType c tv r)]
              , RType c tv r)
bkImplicit (RImpF x tx t _) = ((x,tx):acc, t')
  where (acc,t') = bkImplicit t
bkImplicit t = ([],t)

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
  = do r     <- freshPredRef γ e π
       instantiatePreds γ e $ replacePreds "consE" t [(π, r)]

instantiatePreds _ _ t0
  = return t0

-------------------------------------------------------------------
-- | @instantiateStrata@ generates fresh @Strata@ vars and substitutes
--   them inside the body of the type.
-------------------------------------------------------------------

instantiateStrata :: (F.Subable b, Freshable f Integer) => [F.Symbol] -> b -> f b
instantiateStrata ls t = substStrata t ls <$> mapM (\_ -> fresh) ls

substStrata :: F.Subable a => a -> [F.Symbol] -> [F.Symbol] -> a
substStrata t ls ls'   = F.substa f t
  where
    f x                = fromMaybe x $ L.lookup x su
    su                 = zip ls ls'

-------------------------------------------------------------------
cconsLazyLet :: CGEnv
             -> CoreExpr
             -> SpecType
             -> CG ()
cconsLazyLet γ (Let (NonRec x ex) e) t
  = do tx <- trueTy (varType x)
       γ' <- (γ, "Let NonRec") +++= (x', ex, tx)
       cconsE γ' e t
    where
       x' = F.symbol x

cconsLazyLet _ _ _
  = panic Nothing "Constraint.Generate.cconsLazyLet called on invalid inputs"

--------------------------------------------------------------------------------
-- | Bidirectional Constraint Generation: SYNTHESIS ----------------------------
--------------------------------------------------------------------------------
consE :: CGEnv -> CoreExpr -> CG SpecType
--------------------------------------------------------------------------------
consE γ e
  | patternFlag γ
  , Just p <- Rs.lift e
  = consPattern γ (F.notracepp "CONSE-PATTERN: " p) (exprType e)

-- NV (below) is a hack to type polymorphic axiomatized functions
-- no need to check this code with flag, the axioms environment with
-- is empty if there is no axiomatization. 

-- [NOTE: PLE-OPT] We *disable* refined instantiation for 
-- reflected functions inside proofs.
consE γ e'@(App e@(Var x) (Type τ)) | M.member x (aenv γ)
  = do RAllT α te <- checkAll ("Non-all TyApp with expr", e) γ <$> consE γ e
       t          <- {- PLE-OPT -} if isGeneric γ (ty_var_value α) te && not (isPLETerm γ) 
                                     then freshTy_type TypeInstE e τ 
                                     else trueTy τ
       addW        $ WfC γ t
       t'         <- refreshVV t
       tt00       <- instantiatePreds γ e' $ subsTyVar_meet' (ty_var_value α, t') te
       let tt      = subsTyReft γ (ty_var_value α) τ tt00
       return      $ strengthenMeet tt (singletonReft (M.lookup x $ aenv γ) x)

-- NV END HACK

consE γ (Var x)
  = do t <- varRefType γ x
       addLocA (Just x) (getLocation γ) (varAnn γ x t)
       return t

consE _ (Lit c)
  = refreshVV $ uRType $ literalFRefType c

consE γ e'@(App e a@(Type τ))
  = do RAllT α te <- checkAll ("Non-all TyApp with expr", e) γ <$> consE γ e
       t          <- if isGeneric γ (ty_var_value α) te then freshTy_type TypeInstE e τ else trueTy τ
       addW        $ WfC γ t
       t'         <- refreshVV t
       tt0        <- instantiatePreds γ e' (subsTyVar_meet' (ty_var_value α, t') te)
       let tt      = subsTyReft γ (ty_var_value α) τ tt0
       -- NV TODO: embed this step with subsTyVar_meet'
       case rTVarToBind α of
         Just (x, _) -> return $ maybe (checkUnbound γ e' x tt a) (F.subst1 tt . (x,)) (argType τ)
         Nothing     -> return tt

consE γ e'@(App e a) | Just aDict <- getExprDict γ a
  = case dhasinfo (dlookup (denv γ) aDict) (getExprFun γ e) of
      Just riSig -> return (fromRISig riSig)
      _          -> do
        ([], πs, ls, te) <- bkUniv <$> consE γ e
        te0              <- instantiatePreds γ e' $ foldr RAllP te πs
        te'              <- instantiateStrata ls te0
        (γ', te''')      <- dropExists γ te'
        te''             <- dropConstraints γ te'''
        updateLocA {- πs -}  (exprLoc e) te''
        let RFun x tx t _ = checkFun ("Non-fun App with caller ", e') γ te''
        pushConsBind      $ cconsE γ' a tx
        addPost γ'        $ maybe (checkUnbound γ' e' x t a) (F.subst1 t . (x,)) (argExpr γ a)

consE γ e'@(App e a)
  = do ([], πs, ls, te) <- bkUniv <$> consE γ ({- GM.tracePpr ("APP-EXPR: " ++ GM.showPpr (exprType e)) -} e)
       te0              <- instantiatePreds γ e' $ foldr RAllP te πs
       te'              <- instantiateStrata ls te0
       (γ', te''')      <- dropExists γ te'
       te''             <- dropConstraints γ te'''
       updateLocA (exprLoc e) te''
       (hasGhost, γ'', te''')     <- instantiateGhosts γ' te''
       let RFun x tx t _ = checkFun ("Non-fun App with caller ", e') γ te'''
       pushConsBind      $ cconsE γ'' a tx
       tout <- makeSingleton γ'' e' <$> (addPost γ'' $ maybe (checkUnbound γ'' e' x t a) (F.subst1 t . (x,)) (argExpr γ a))
       if hasGhost
          then do
           tk   <- freshTy_type ImplictE e' $ exprType e'
           addW $ WfC γ tk
           addC (SubC γ'' tout tk) ""
           return tk
          else return tout

consE γ (Lam α e) | isTyVar α
  = do γ' <- updateEnvironment γ α
       liftM (RAllT (makeRTVar $ rTyVar α)) (consE γ' e)

consE γ  e@(Lam x e1)
  = do tx      <- freshTy_type LamE (Var x) τx
       γ'      <- γ += ("consE", F.symbol x, tx)
       t1      <- consE γ' e1
       addIdA x $ AnnDef tx
       addW     $ WfC γ tx
       tce     <- tyConEmbed <$> get
       return   $ RFun (F.symbol x) tx t1 $ lambdaSingleton (addArgument γ x) tce x e1
    where
      FunTy τx _ = exprType e

consE γ e@(Let _ _)
  = cconsFreshE LetE γ e

consE γ e@(Case _ _ _ [_])
  | Just p@(Rs.PatProject {}) <- Rs.lift e
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

consE _ e@(Coercion _)
   = trueTy $ exprType e

consE _ e@(Type t)
  = panic Nothing $ "consE cannot handle type " ++ GM.showPpr (e, t)

caseKVKind ::[Alt Var] -> KVKind
caseKVKind [(DataAlt _, _, Var _)] = ProjectE
caseKVKind cs                      = CaseE (length cs)

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
  mt <- consE γ' e2
  return mt
  where
    msg = "This expression has a refined monadic type; run with --no-pattern-inline: "

{- [NOTE] special type rule for monadic-return

           G |- e ~> et
    ------------------------
      G |- return e ~ m et
 -}
consPattern γ (Rs.PatReturn e m _ _ _) t = do
  et    <- F.notracepp "Cons-Pattern-Ret" <$> consE γ e
  mt    <- trueTy  m
  tt    <- trueTy  t
  return (mkRAppTy mt et tt) -- /// {-    $ RAppTy mt et mempty -}

{- [NOTE] special type rule for field projection, is
          t  = G(x)       ti = Proj(t, i)
    -----------------------------------------
      G |- case x of C [y1...yn] -> yi : ti
 -}

consPattern γ (Rs.PatProject xe _ τ c ys i) _ = do
  let yi = ys !! i
  t    <- (addW . WfC γ) <<= freshTy_type ProjectE (Var yi) τ
  γ'   <- caseEnv γ xe [] (DataAlt c) ys (Just [i])
  ti   <- {- γ' ??= yi -} varRefType γ' yi
  addC (SubC γ' ti t) "consPattern:project"
  return t

consPattern γ (Rs.PatSelfBind _ e) _ =
  consE γ e

consPattern γ p@(Rs.PatSelfRecBind {}) _ =
  cconsFreshE LetE γ (Rs.lower p)

mkRAppTy :: SpecType -> SpecType -> SpecType -> SpecType 
mkRAppTy mt et (RAppTy _ _ _)    = RAppTy mt et mempty 
mkRAppTy _  et (RApp c [_] [] _) = RApp c [et] [] mempty 
mkRAppTy _  _  _                 = panic Nothing $ "Unexpected return-pattern" 

checkMonad :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkMonad x g = go . unRRTy
 where
   go (RApp _ ts [] _)
     | length ts > 0 = last ts
   go (RAppTy _ t _) = t
   go t              = checkErr x g t

unRRTy :: SpecType -> SpecType
unRRTy (RRTy _ _ _ t) = unRRTy t
unRRTy t              = t

--------------------------------------------------------------------------------
castTy  :: CGEnv -> Type -> CoreExpr -> Coercion -> CG SpecType
castTy' :: CGEnv -> Type -> CoreExpr -> CG SpecType
--------------------------------------------------------------------------------
castTy γ t e (AxiomInstCo ca _ _)
  = fromMaybe <$> castTy' γ t e <*> lookupNewType (coAxiomTyCon ca)

castTy γ t e (SymCo (AxiomInstCo ca _ _))
  = do mtc <- lookupNewType (coAxiomTyCon ca)
       case mtc of
        Just tc -> cconsE γ e tc
        Nothing -> return ()
       castTy' γ t e

castTy γ t e _
  = castTy' γ t e


castTy' _ τ (Var x)
  = do t <- trueTy τ
       return (t `strengthen` (uTop $ F.uexprReft $ F.expr x))

castTy' γ t (Tick _ e)
  = castTy' γ t e

castTy' _ _ e
  = panic Nothing $ "castTy cannot handle expr " ++ GM.showPpr e

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
  , [tm]    <- dataConOrigArgTys dc
               -- tcMatchTy because we have to instantiate the class tyvars
  , Just _  <- ruleMatchTyX (mkUniqSet $ tyConTyVars tc) (mkRnEnv2 emptyInScopeSet) emptyTvSubstEnv tm t1
  = Just (\e -> mkCoreConApps dc $ map Type ts ++ [e])

  | otherwise
  = Nothing
  where
    ruleMatchTyX =ruleMatchTyKiX -- TODO: is this correct?

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
  t   <- freshTy_type kvkind e $ exprType e
  addW $ WfC γ t
  cconsE γ e t
  return t
--------------------------------------------------------------------------------

checkUnbound :: (Show a, Show a2, F.Subable a)
             => CGEnv -> CoreExpr -> F.Symbol -> a -> a2 -> a
checkUnbound γ e x t a
  | x `notElem` (F.syms t) = t
  | otherwise              = panic (Just $ getLocation γ) msg
  where
    msg = unlines [ "checkUnbound: " ++ show x ++ " is elem of syms of " ++ show t
                  , "In", GM.showPpr e, "Arg = " , show a ]


dropExists :: CGEnv -> SpecType -> CG (CGEnv, SpecType)
dropExists γ (REx x tx t) =         (, t) <$> γ += ("dropExists", x, tx)
dropExists γ t            = return (γ, t)

dropConstraints :: CGEnv -> SpecType -> CG SpecType
dropConstraints γ (RFun x tx@(RApp c _ _ _) t r) | isClass c
  = (flip (RFun x tx)) r <$> dropConstraints γ t
dropConstraints γ (RRTy cts _ OCons t)
  = do γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("splitS", x,t)) γ xts
       addC (SubC  γ' t1 t2)  "dropConstraints"
       dropConstraints γ t
  where
    (xts, t1, t2) = envToSub cts

dropConstraints _ t = return t

-------------------------------------------------------------------------------------
cconsCase :: CGEnv -> Var -> SpecType -> [AltCon] -> (AltCon, [Var], CoreExpr) -> CG ()
-------------------------------------------------------------------------------------
cconsCase γ x t acs (ac, ys, ce)
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
  let xt           = shiftVV xt0 x'
  tdc             <- (γ ??= (dataConWorkId c) >>= refreshVV)
  let (rtd,yts',_) = unfoldR tdc xt ys
  yts             <- projectTypes pIs yts'
  let ys''         = F.symbol <$> filter (not . GM.isPredVar) ys
  let r1           = dataConReft   c   ys''
  let r2           = dataConMsReft rtd ys''
  let xt           = (xt0 `F.meet` rtd) `strengthen` (uTop (r1 `F.meet` r2))
  let cbs          = safeZip "cconsCase" (x':ys') (xt0 : yts)
  cγ'             <- addBinders γ   x' cbs
  cγ              <- addBinders cγ' x' [(x', xt)]
  return           $ addArguments cγ ys
  -- where
    -- ys'' = F.symbol <$> (filter (not . isClassPred . varType) ys)

caseEnv γ x acs a _ _ = do 
  let x'  = F.symbol x
  xt'    <- (`strengthen` uTop (altReft γ acs a)) <$> (γ ??= x)
  cγ     <- addBinders γ x' [(x', xt')]
  return cγ

--------------------------------------------------------------------------------
-- | `projectTypes` masks (i.e. true's out) all types EXCEPT those
--   at given indices; it is used to simplify the environment used
--   when projecting out fields of single-ctor datatypes.
--------------------------------------------------------------------------------
projectTypes :: Maybe [Int] -> [SpecType] -> CG [SpecType]
projectTypes Nothing   ts = return ts
projectTypes (Just is) ts = mapM (projT is) (zip [0..] ts)
  where
    projT is (j, t)
      | j `elem` is       = return t
      | otherwise         = true t

altReft :: CGEnv -> [AltCon] -> AltCon -> F.Reft
altReft _ _ (LitAlt l)   = literalFReft l
altReft γ acs DEFAULT    = mconcat ([notLiteralReft l | LitAlt l <- acs] ++ [notDataConReft d | DataAlt d <- acs])
  where
    notLiteralReft   = maybe mempty F.notExprReft . snd . literalConst (emb γ)
    notDataConReft d | exactDC (getConfig γ)
                     = F.Reft (F.vv_, F.PNot (F.EApp (F.EVar $ makeDataConChecker d) (F.EVar F.vv_)))
                     | otherwise = mempty
altReft _ _ _        = panic Nothing "Constraint : altReft"

unfoldR :: SpecType -> SpecType -> [Var] -> (SpecType, [SpecType], SpecType)
unfoldR td (RApp _ ts rs _) ys = (t3, tvys ++ yts, ignoreOblig rt)
  where
        tbody              = instantiatePvs (instantiateTys td ts) (reverse rs)
        -- TODO: if we ever want to support applying implicits explicitly, will need to rejigger
        ((_,_,_),(ys0,yts',_), rt) = safeBkArrow (F.notracepp msg $ instantiateTys tbody tvs')
        msg                = "INST-TY: " ++ F.showpp (td, ts, tbody, ys, tvs') 
        yts''              = zipWith F.subst sus (yts'++[rt])
        (t3,yts)           = (last yts'', init yts'')
        sus                = F.mkSubst <$> (L.inits [(x, F.EVar y) | (x, y) <- zip ys0 ys'])
        (αs, ys')          = mapSnd (F.symbol <$>) $ L.partition isTyVar ys
        tvs' :: [SpecType]
        tvs'               = rVar <$> αs
        tvys               = ofType . varType <$> αs

unfoldR _  _                _  = panic Nothing "Constraint.hs : unfoldR"

instantiateTys :: SpecType -> [SpecType] -> SpecType
instantiateTys = L.foldl' go
  where 
    go (RAllT α tbody) t = subsTyVar_meet' (ty_var_value α, t) tbody
    go _ _               = panic Nothing "Constraint.instantiateTy"

instantiatePvs :: SpecType -> [SpecProp] -> SpecType
instantiatePvs           = L.foldl' go
  where 
    go (RAllP p tbody) r = replacePreds "instantiatePv" tbody [(p, r)]
    go t               _ = errorP "" ("Constraint.instantiatePvs: t = " ++ showpp t)

checkTyCon :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkTyCon _ _ t@(RApp _ _ _ _) = t
checkTyCon x g t                = checkErr x g t

checkFun :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkFun _ _ t@(RFun _ _ _ _) = t
checkFun x g t                = checkErr x g t

checkAll :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkAll _ _ t@(RAllT _ _)    = t
checkAll x g t                = checkErr x g t

checkErr :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkErr (msg, e) γ t         = panic (Just sp) $ msg ++ GM.showPpr e ++ ", type: " ++ showpp t
  where
    sp                        = getLocation γ

varAnn :: CGEnv -> Var -> t -> Annot t
varAnn γ x t
  | x `S.member` recs γ      = AnnLoc (getSrcSpan x)
  | otherwise                = AnnUse t

-----------------------------------------------------------------------
-- | Helpers: Creating Fresh Refinement -------------------------------
-----------------------------------------------------------------------
freshPredRef :: CGEnv -> CoreExpr -> PVar RSort -> CG SpecProp
freshPredRef γ e (PV _ (PVProp τ) _ as)
  = do t    <- freshTy_type PredInstE e (toType τ)
       args <- mapM (\_ -> fresh) as
       let targs = [(x, s) | (x, (s, y, z)) <- zip args as, (F.EVar y) == z ]
       γ' <- foldM (+=) γ [("freshPredRef", x, ofRSort τ) | (x, τ) <- targs]
       addW $ WfC γ' t
       return $ RProp targs t

freshPredRef _ _ (PV _ PVHProp _ _)
  = todo Nothing "EFFECTS:freshPredRef"


--------------------------------------------------------------------------------
-- | Helpers: Keep track of polymorphic let bindings  --------------------------
--------------------------------------------------------------------------------

addRankNBind :: CGEnv -> Var -> CoreExpr -> CGEnv     
addRankNBind γ x e 
  | rankNTypes (getConfig γ)
  , isForAllTy (varType x)
  , Just e' <- forallExpr γ e 
  = γ {forallcb = M.insert x e' (forallcb γ)}
addRankNBind γ _ _  
  = γ


--------------------------------------------------------------------------------
-- | Helpers: Creating Refinement Types For Various Things ---------------------
--------------------------------------------------------------------------------
argType :: Type -> Maybe F.Expr
argType (LitTy (NumTyLit i))
  = mkI i
argType (LitTy (StrTyLit s))
  = mkS $ fastStringToByteString s
argType (TyVarTy x)
  = Just $ F.EVar $ F.symbol $ varName x
argType t
  | F.symbol (GM.showPpr t) == anyTypeSymbol
  = Just $ F.EVar anyTypeSymbol
argType _
  = Nothing


argExpr :: CGEnv -> CoreExpr -> Maybe F.Expr
argExpr γ (Var v)     | M.member v $ aenv γ, higherOrderFlag γ
                      = F.EVar <$> (M.lookup v $ aenv γ)
argExpr _ (Var vy)    = Just $ F.eVar vy
argExpr γ (Lit c)     = snd  $ literalConst (emb γ) c
argExpr γ (Tick _ e)  = argExpr γ e
argExpr _ _           = Nothing


-- NIKI TODO: merge arg/lam/fun-Expr
lamExpr :: CGEnv -> CoreExpr -> Maybe F.Expr
lamExpr γ (Var v)     | M.member v $ aenv γ
                      = F.EVar <$> (M.lookup v $ aenv γ)
lamExpr γ (Var v)     | S.member v (fargs γ)
                      =  Just $ F.eVar v
lamExpr γ (Lit c)     = snd  $ literalConst (emb γ) c
lamExpr γ (Tick _ e)  = lamExpr γ e
lamExpr γ (App e (Type _)) = lamExpr γ e
lamExpr γ (App e1 e2) = case (lamExpr γ e1, lamExpr γ e2) of
                              (Just p1, Just p2) | not (GM.isPredExpr e2) -- (isClassPred $ exprType e2)
                                                 -> Just $ F.EApp p1 p2
                              (Just p1, Just _ ) -> Just p1
                              _  -> Nothing
lamExpr γ (Let (NonRec x ex) e) = case (lamExpr γ ex, lamExpr (addArgument γ x) e) of
                                       (Just px, Just p) -> Just (p `F.subst1` (F.symbol x, px))
                                       _  -> Nothing
lamExpr γ (Lam x e)   = case lamExpr (addArgument γ x) e of
                            Just p -> Just $ F.ELam (F.symbol x, typeSort (emb γ) $ varType x) p
                            _ -> Nothing
lamExpr _ _           = Nothing



forallExpr :: CGEnv -> CoreExpr -> Maybe F.Expr
forallExpr γ (Var v)          | M.member v $ aenv γ, higherOrderFlag γ
                              = F.EVar <$> (M.lookup v $ aenv γ)
forallExpr _ (Var vy)         = Just $ F.eVar vy
forallExpr γ (Lit c)          = snd  $ literalConst (emb γ) c
forallExpr γ (Lam a e)        | isTyVar a 
                              = forallExpr γ e 
forallExpr γ (Tick _ e)       = forallExpr γ e
forallExpr γ (App e (Type _)) = forallExpr γ e
forallExpr γ (App e1 e2)      = case (forallExpr γ e1, forallExpr γ e2) of
                                  (Just p1, Just p2) -> Just $ F.EApp p1 p2 
                                  _                  -> Nothing 
forallExpr _ _                = Nothing


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
varRefType γ x = do
  xt <- varRefType' γ x <$> (γ ??= x)
  return xt -- F.tracepp (printf "varRefType x = [%s]" (showpp x))

varRefType' :: CGEnv -> Var -> SpecType -> SpecType
varRefType' γ x t'
  | Just tys <- trec γ, Just tr  <- M.lookup x' tys
  = strengthen tr xr
  | otherwise
  = strengthen t' xr
  where
    xr = singletonReft (M.lookup x $ aenv γ) x
    x' = F.symbol x
    strengthen
      | higherOrderFlag γ
      = strengthenMeet
      | otherwise
      = strengthenTop

-- | create singleton types for function application
makeSingleton :: CGEnv -> CoreExpr -> SpecType -> SpecType
makeSingleton γ e t
  | higherOrderFlag γ, App f x <- simplify e
  = case (funExpr γ f, argForAllExpr x) of
      (Just f', Just x')
                 | not (GM.isPredExpr x) -- (isClassPred $ exprType x)
                 -> strengthenMeet t (uTop $ F.exprReft (F.EApp f' x'))
      (Just f', Just _)
                 -> strengthenMeet t (uTop $ F.exprReft f' )
      _ -> t
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

-- reflectefd functions
funExpr γ (Var v) | M.member v $ aenv γ
  = F.EVar <$> (M.lookup v $ aenv γ)

-- local function arguments
funExpr γ (Var v) | S.member v (fargs γ) || GM.isDataConId v
  = Just $ F.EVar (F.symbol v)

funExpr γ (App e1 e2)
  = case (funExpr γ e1, argExpr γ e2) of
      (Just e1', Just e2') | not (GM.isPredExpr e2) -- (isClassPred $ exprType e2)
                           -> Just (F.EApp e1' e2')
      (Just e1', Just _)
                           -> Just e1'
      _                    -> Nothing

funExpr _ _
  = Nothing

simplify :: CoreExpr -> CoreExpr
simplify (Tick _ e)       = simplify e
simplify (App e (Type _)) = simplify e
simplify (App e1 e2)      = App (simplify e1) (simplify e2)
simplify e                = e


singletonReft :: (F.Symbolic a, F.Symbolic a1) => Maybe a -> a1 -> UReft F.Reft
singletonReft (Just x) _ = uTop $ F.symbolReft x
singletonReft Nothing  v = uTop $ F.symbolReft $ F.symbol v

-- | RJ: `nomeet` replaces `strengthenS` for `strengthen` in the definition
--   of `varRefType`. Why does `tests/neg/strata.hs` fail EVEN if I just replace
--   the `otherwise` case? The fq file holds no answers, both are sat.
strengthenTop :: (PPrint r, F.Reftable r) => RType c tv r -> r -> RType c tv r
strengthenTop (RApp c ts rs r) r'  = RApp c ts rs $ F.meet r r'
strengthenTop (RVar a r) r'        = RVar a       $ F.meet r r'
strengthenTop (RFun b t1 t2 r) r'  = RFun b t1 t2 $ F.meet r r'
strengthenTop (RAppTy t1 t2 r) r'  = RAppTy t1 t2 $ F.meet r r'
strengthenTop t _                  = t

-- TODO: this is almost identical to RT.strengthen! merge them!
strengthenMeet :: (PPrint r, F.Reftable r) => RType c tv r -> r -> RType c tv r
strengthenMeet (RApp c ts rs r) r'  = RApp c ts rs (r `F.meet` r')
strengthenMeet (RVar a r) r'        = RVar a       (r `F.meet` r')
strengthenMeet (RFun b t1 t2 r) r'  = RFun b t1 t2 (r `F.meet` r')
strengthenMeet (RAppTy t1 t2 r) r'  = RAppTy t1 t2 (r `F.meet` r')
strengthenMeet (RAllT a t) r'       = RAllT a $ strengthenMeet t r'
strengthenMeet t _                  = t

-- topMeet :: (PPrint r, F.Reftable r) => r -> r -> r
-- topMeet r r' = r `F.meet` r'

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

-- | @isGeneric@ determines whether the @RTyVar@ CAN and SHOULD be instantiated in a refined manner.
isGeneric :: CGEnv -> RTyVar -> SpecType -> Bool
isGeneric γ α t = isGenericVar α t && not (isPLETerm γ)

-- | @isPLETerm γ@ returns @True@ if the "currrent" top-level binder in γ has PLE enabled.
isPLETerm :: CGEnv -> Bool  
isPLETerm γ 
  | Just x <- cgVar γ = {- F.tracepp ("isPLEVar:" ++ F.showpp x) $ -} isPLEVar (giSpec . cgInfo $ γ) x 
  | otherwise         = False 

-- | @isGenericVar@ determines whether the @RTyVar@ has no class constraints
isGenericVar :: RTyVar -> SpecType -> Bool
isGenericVar α t =  all (\(c, α') -> (α'/=α) || isOrd c || isEq c ) (classConstrs t)
  where 
    classConstrs t = [(c, ty_var_value α')
                        | (c, ts) <- tyClasses t
                        , t'      <- ts
                        , α'      <- freeTyVars t']
    isOrd          = (ordClassName ==) . className
    isEq           = (eqClassName ==) . className

-- instance MonadFail CG where 
--  fail msg = panic Nothing msg

instance MonadFail Data.Functor.Identity.Identity where 
  fail msg = panic Nothing msg
