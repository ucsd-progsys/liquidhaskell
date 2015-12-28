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

-- | This module defines the representation of Subtyping and WF Constraints, and
-- the code for syntax-directed constraint generation.

module Language.Haskell.Liquid.Constraint.Generate ( generateConstraints ) where

import GHC.Err.Located hiding (error)
import GHC.Stack

import CoreUtils     (exprType)
import MkCore
import Coercion
import DataCon
import Pair
import CoreSyn
import SrcLoc
import Type
import TyCon
import PrelNames
import TypeRep
import Class            (Class, className)
import Var
import Kind
import Id
import IdInfo
import Name
import NameSet
import TypeRep
import Unique

import Text.PrettyPrint.HughesPJ hiding (first)

import Control.Monad.State

import Control.Applicative      ((<$>), (<*>), Applicative)

import Data.Monoid              (mconcat, mempty, mappend)
import Data.Maybe               (fromMaybe, catMaybes, fromJust, isJust)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L
import qualified Data.Text           as T
import Data.Bifunctor
import qualified Data.Foldable    as F
import qualified Data.Traversable as T
import qualified Control.Exception as Ex

import Text.Printf

import           Language.Haskell.Liquid.UX.PrettyPrint -- (pprint)
import qualified Language.Haskell.Liquid.UX.CTags       as Tg
import           Language.Haskell.Liquid.UX.Errors
import Language.Fixpoint.SortCheck (pruneUnsortedReft)
import Language.Fixpoint.Types.Visitor
import Language.Fixpoint.Types.Names (symbolString)
import Language.Haskell.Liquid.Constraint.Fresh
import Language.Haskell.Liquid.Constraint.Env
import Language.Haskell.Liquid.Constraint.Monad
import Language.Haskell.Liquid.Constraint.Split

import qualified Language.Fixpoint.Types            as F

import Language.Haskell.Liquid.WiredIn          (dictionaryVar)
import Language.Haskell.Liquid.Types.Dictionaries
import Language.Haskell.Liquid.Types.Variance
import Language.Haskell.Liquid.Types            hiding (binds, Loc, loc, freeTyVars, Def)
import Language.Haskell.Liquid.Types.Strata
import Language.Haskell.Liquid.Types.Names
import Language.Haskell.Liquid.Types.Bounds
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Types.Visitors         hiding (freeVars)
import Language.Haskell.Liquid.Types.PredType         hiding (freeTyVars)
import Language.Haskell.Liquid.GHC.Misc          ( isInternal, collectArguments, tickSrcSpan
                                                 , hasBaseTypeVar, showPpr, isDataConId
                                                 , symbolFastString, stringVar, stringTyVar)
import Language.Haskell.Liquid.Misc
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.Types.Literals

import Language.Haskell.Liquid.Constraint.Axioms
import Language.Haskell.Liquid.Constraint.Types
import Language.Haskell.Liquid.Constraint.Constraint

-- import Debug.Trace (trace)

-----------------------------------------------------------------------
------------- Constraint Generation: Toplevel -------------------------
-----------------------------------------------------------------------

generateConstraints      :: GhcInfo -> CGInfo
generateConstraints info = {-# SCC "ConsGen" #-} execState act $ initCGI cfg info
  where
    act                  = consAct info
    cfg                  = config $ spec info

consAct :: GhcInfo -> CG ()
consAct info
  = do γ'    <- initEnv      info
       sflag <- scheck   <$> get
       tflag <- trustghc <$> get
       γ     <- if expandProofsMode then addCombine τProof γ' else return γ'
       cbs'  <- if expandProofsMode then mapM (expandProofs info (mkSigs γ)) $ cbs info else return $ cbs info
       let trustBinding x = tflag && (x `elem` derVars info || isInternal x)
       foldM_ (consCBTop trustBinding) γ cbs'
       hcs   <- hsCs  <$> get
       hws   <- hsWfs <$> get
       scss  <- sCs   <$> get
       annot <- annotMap <$> get
       scs   <- if sflag then concat <$> mapM splitS (hcs ++ scss)
                         else return []
       let smap = if sflag then solveStrata scs else []
       let hcs' = if sflag then subsS smap hcs else hcs
       fcs <- concat <$> mapM splitC (subsS smap hcs')
       fws <- concat <$> mapM splitW hws
       let annot' = if sflag then subsS smap <$> annot else annot
       modify $ \st -> st { fEnv = fixEnv γ, fixCs = fcs , fixWfs = fws , annotMap = annot'}
  where
    mkSigs γ = case (grtys γ,  assms γ, renv γ) of
                (REnv g1, REnv g2, REnv g3) -> (M.toList g3) ++ (M.toList g2) ++ (M.toList g1)
    expandProofsMode = autoproofs $ config $ spec info
    τProof           = proofType $ spec info
    fixEnv   = feEnv . fenv

addCombine τ γ
  = do t <- trueTy combineType
       γ ++= ("combineProofs", combineSymbol, t)
  where
    combineType   = makeCombineType τ
    combineVar    = makeCombineVar  combineType
    combineSymbol = F.symbol combineVar

------------------------------------------------------------------------------------
initEnv :: GhcInfo -> CG CGEnv
------------------------------------------------------------------------------------
initEnv info
  = do let tce   = tcEmbeds sp
       let fVars = impVars info
       let dcs   = filter isConLikeId ((snd <$> freeSyms sp))
       let dcs'  = filter isConLikeId fVars
       defaults <- forM fVars $ \x -> liftM (x,) (trueTy $ varType x)
       dcsty    <- forM dcs   $ makeDataConTypes
       dcsty'   <- forM dcs'  $ makeDataConTypes
       (hs,f0)  <- refreshHoles $ grty info                  -- asserted refinements     (for defined vars)
       f0''     <- refreshArgs' =<< grtyTop info             -- default TOP reftype      (for exported vars without spec)
       let f0'   = if notruetypes $ config sp then [] else f0''
       f1       <- refreshArgs'   defaults                   -- default TOP reftype      (for all vars)
       f1'      <- refreshArgs' $ makedcs dcsty
       f2       <- refreshArgs' $ assm info                  -- assumed refinements      (for imported vars)
       f3       <- refreshArgs' $ vals asmSigs sp            -- assumed refinedments     (with `assume`)
       f40      <- refreshArgs' $ vals ctors sp              -- constructor refinements  (for measures)
       (invs1, f41) <- mapSndM refreshArgs' $ makeAutoDecrDataCons dcsty  (autosize sp) dcs
       (invs2, f42) <- mapSndM refreshArgs' $ makeAutoDecrDataCons dcsty' (autosize sp) dcs'
       let f4    = mergeDataConTypes (mergeDataConTypes f40 (f41 ++ f42)) (filter (isDataConId . fst) f2)
       sflag    <- scheck <$> get
       let senv  = if sflag then f2 else []
       let tx    = mapFst F.symbol . addRInv ialias . strataUnify senv . predsUnify sp
       let bs    = (tx <$> ) <$> [f0 ++ f0', f1 ++ f1', f2, f3, f4]
       lts      <- lits <$> get
       let tcb   = mapSnd (rTypeSort tce) <$> concat bs
       let γ0    = measEnv sp (head bs) (cbs info) (tcb ++ lts) (bs!!3) hs (invs1 ++ invs2)
       foldM (++=) γ0 [("initEnv", x, y) | (x, y) <- concat $ tail bs]
  where
    sp           = spec info
    ialias       = mkRTyConIAl $ ialiases sp
    vals f       = map (mapSnd val) . f
    mapSndM f (x,y) = (x,) <$> f y
    makedcs      = map strengthenDataConType

makeDataConTypes x = (x,) <$> (trueTy $ varType x)

makeAutoDecrDataCons dcts specenv dcs
  = (simplify invs, tys)
  where
    (invs, tys) = unzip $ concatMap go tycons
    tycons      = L.nub $ catMaybes $ map idTyCon dcs

    go tycon
      | S.member tycon specenv =  zipWith (makeSizedDataCons dcts) (tyConDataCons tycon) [0..]
    go _
      = []
    idTyCon x = dataConTyCon <$> case idDetails x of {DataConWorkId d -> Just d; DataConWrapId d -> Just d; _ -> Nothing}

    simplify invs = dummyLoc . (`strengthen` invariant) .  fmap (\_ -> mempty) <$> L.nub invs
    invariant = MkUReft (F.Reft (F.vv_, F.PAtom F.Ge (lenOf F.vv_) (F.ECon $ F.I 0)) ) mempty mempty

lenOf x = F.EApp lenLocSymbol [F.EVar x]

makeSizedDataCons dcts x' n = (toRSort $ ty_res trep, (x, fromRTypeRep trep{ty_res = tres}))
    where
      x      = dataConWorkId x'
      t      = fromMaybe (errorstar "makeSizedDataCons: this should never happen") $ L.lookup x dcts
      trep   = toRTypeRep t
      tres   = ty_res trep `strengthen` MkUReft (F.Reft (F.vv_, F.PAtom F.Eq (lenOf F.vv_) computelen)) mempty mempty

      recarguments = filter (\(t,_) -> (toRSort t == toRSort tres)) (zip (ty_args trep) (ty_binds trep))
      computelen   = foldr (F.EBin F.Plus) (F.ECon $ F.I n) (lenOf .  snd <$> recarguments)


mergeDataConTypes xts yts = merge (L.sortBy f xts) (L.sortBy f yts)
  where
    f (x,_) (y,_) = compare x y
    merge [] ys = ys
    merge xs [] = xs
    merge (xt@(x, tx):xs) (yt@(y, ty):ys)
      | x == y    = (x, tx `F.meet` ty):merge xs ys
      | x <  y    = xt:merge xs (yt:ys)
      | otherwise = yt:merge (xt:xs) ys

refreshHoles vts = first catMaybes . unzip . map extract <$> mapM refreshHoles' vts
refreshHoles' (x,t)
  | noHoles t = return (Nothing, x, t)
  | otherwise = (Just $ F.symbol x,x,) <$> mapReftM tx t
  where
    tx r | hasHole r = refresh r
         | otherwise = return r
extract (a,b,c) = (a,(b,c))

refreshArgs' = mapM (mapSndM refreshArgs)

strataUnify :: [(Var, SpecType)] -> (Var, SpecType) -> (Var, SpecType)
strataUnify senv (x, t) = (x, maybe t (mappend t) pt)
  where
    pt                  = fmap (\(MkUReft _ _ l) -> MkUReft mempty mempty l) <$> L.lookup x senv


-- | TODO: All this *should* happen inside @Bare@ but appears
--   to happen after certain are signatures are @fresh@-ed,
--   which is why they are here.

-- NV : still some sigs do not get TyConInfo

predsUnify :: GhcSpec -> (Var, RRType RReft) -> (Var, RRType RReft)
predsUnify sp = second (addTyConInfo tce tyi) -- needed to eliminate some @RPropH@

  where
    tce            = tcEmbeds sp
    tyi            = tyconEnv sp

 -------------------------------------------------------------------------------
 -------------------------------------------------------------------------------
 -------------------------------------------------------------------------------

measEnv sp xts cbs lts asms hs autosizes
  = CGE { loc   = noSrcSpan
        , renv  = fromListREnv $ second val <$> meas sp
        , syenv = F.fromListSEnv $ freeSyms sp
        , fenv  = initFEnv $ lts ++ (second (rTypeSort tce . val) <$> meas sp)
        , denv  = dicts sp
        , recs  = S.empty
        , invs  = mkRTyConInv    $ (invariants sp ++ autosizes)
        , ial   = mkRTyConIAl    $ ialiases   sp
        , grtys = fromListREnv xts
        , assms = fromListREnv asms
        , emb   = tce
        , tgEnv = Tg.makeTagEnv cbs
        , tgKey = Nothing
        , trec  = Nothing
        , lcb   = M.empty
        , holes = fromListHEnv hs
        , lcs   = mempty
        }
    where
      tce = tcEmbeds sp

assm = assmGrty impVars
grty = assmGrty defVars

assmGrty f info = [ (x, val t) | (x, t) <- sigs, x `S.member` xs ]
  where
    xs          = S.fromList $ f info
    sigs        = tySigs     $ spec info

grtyTop info     = forM topVs $ \v -> (v,) <$> trueTy (varType v)
  where
    topVs        = filter isTop $ defVars info
    isTop v      = isExportedId v && not (v `S.member` sigVs)
    isExportedId = flip elemNameSet (exports $ spec info) . getName
    sigVs        = S.fromList [v | (v,_) <- tySigs (spec info) ++ asmSigs (spec info)]


------------------------------------------------------------------------
-- | Helpers: Reading/Extending Environment Bindings -------------------
------------------------------------------------------------------------



setLoc :: CGEnv -> SrcSpan -> CGEnv
γ `setLoc` src
  | isGoodSrcSpan src = γ { loc = src }
  | otherwise         = γ

withRecs :: CGEnv -> [Var] -> CGEnv
withRecs γ xs  = γ { recs = L.foldl' (flip S.insert) (recs γ) xs }

withTRec γ xts = γ' {trec = Just $ M.fromList xts' `M.union` trec'}
  where γ'    = γ `withRecs` (fst <$> xts)
        trec' = fromMaybe M.empty $ trec γ
        xts'  = mapFst F.symbol <$> xts

setBind :: CGEnv -> Tg.TagKey -> CGEnv
setBind γ k
  | Tg.memTagEnv k (tgEnv γ) = γ { tgKey = Just k }
  | otherwise                = γ



initCGI cfg info = CGInfo {
    fEnv       = F.emptySEnv
  , hsCs       = []
  , sCs        = []
  , hsWfs      = []
  , fixCs      = []
  , isBind     = []
  , fixWfs     = []
  , freshIndex = 0
  , binds      = F.emptyBindEnv
  , annotMap   = AI M.empty
  , tyConInfo  = tyi
  , tyConEmbed = tce
  , kuts       = mempty -- F.ksEmpty
  , lits       = coreBindLits tce info ++  (map (mapSnd F.sr_sort) $ map mkSort $ meas spc)
  , termExprs  = M.fromList $ texprs spc
  , specDecr   = decr spc
  , specLVars  = lvars spc
  , specLazy   = dictionaryVar `S.insert` lazy spc
  , tcheck     = not $ notermination cfg
  , scheck     = strata cfg
  , trustghc   = trustinternals cfg
  , pruneRefs  = not $ noPrune cfg
  , logErrors  = []
  , kvProf     = emptyKVProf
  , recCount   = 0
  , bindSpans  = M.empty
  , autoSize   = autosize spc
  }
  where
    tce        = tcEmbeds spc
    spc        = spec info
    tyi        = tyconEnv spc -- EFFECTS HEREHEREHERE makeTyConInfo (tconsP spc)

    mkSort = mapSnd (rTypeSortedReft tce . val)

coreBindLits :: F.TCEmb TyCon -> GhcInfo -> [(F.Symbol, F.Sort)]
coreBindLits tce info
  = sortNub      $ [ (F.symbol x, F.strSort) | (_, Just (F.ESym x)) <- lconsts ]    -- strings
                ++ [ (dconToSym dc, dconToSort dc) | dc <- dcons ]                  -- data constructors
  where
    lconsts      = literalConst tce <$> literals (cbs info)
    dcons        = filter isDCon freeVs
    freeVs       = impVars info ++ (snd <$> freeSyms (spec info))
    dconToSort   = typeSort tce . expandTypeSynonyms . varType
    dconToSym    = F.symbol . idDataCon
    isDCon x     = isDataConId x && not (hasBaseTypeVar x)

-------------------------------------------------------------------
------------------------ Generation: Freshness --------------------
-------------------------------------------------------------------

-- | Right now, we generate NO new pvars. Rather than clutter code
--   with `uRType` calls, put it in one place where the above
--   invariant is /obviously/ enforced.
--   Constraint generation should ONLY use @freshTy_type@ and @freshTy_expr@

freshTy_type        :: KVKind -> CoreExpr -> Type -> CG SpecType
freshTy_type k _ τ  = freshTy_reftype k $ ofType τ

freshTy_expr        :: KVKind -> CoreExpr -> Type -> CG SpecType
freshTy_expr k e _  = freshTy_reftype k $ exprRefType e

freshTy_reftype     :: KVKind -> SpecType -> CG SpecType
-- freshTy_reftype k t = do t <- refresh =<< fixTy t
--                          addKVars k t
--                          return t

freshTy_reftype k t = (fixTy t >>= refresh) =>> addKVars k

-- | Used to generate "cut" kvars for fixpoint. Typically, KVars for recursive
--   definitions, and also to update the KVar profile.

addKVars        :: KVKind -> SpecType -> CG ()
addKVars !k !t  = do when (True)    $ modify $ \s -> s { kvProf = updKVProf k kvars (kvProf s) }
                     when (isKut k) $ modify $ \s -> s { kuts   = mappend   kvars   (kuts s)   }
  where
     kvars      = F.KS $ S.fromList $ specTypeKVars t

isKut          :: KVKind -> Bool
isKut RecBindE = True
isKut _        = False

specTypeKVars :: SpecType -> [F.KVar]
specTypeKVars = foldReft (\ _ r ks -> (kvars $ ur_reft r) ++ ks) []

trueTy  :: Type -> CG SpecType
trueTy = ofType' >=> true

ofType' :: Type -> CG SpecType
ofType' = fixTy . ofType

fixTy :: SpecType -> CG SpecType
fixTy t = do tyi   <- tyConInfo  <$> get
             tce   <- tyConEmbed <$> get
             return $ addTyConInfo tce tyi t

refreshArgsTop :: (Var, SpecType) -> CG SpecType
refreshArgsTop (x, t)
  = do (t', su) <- refreshArgsSub t
       modify $ \s -> s {termExprs = M.adjust (F.subst su <$>) x $ termExprs s}
       return t'

refreshArgs :: SpecType -> CG SpecType
refreshArgs t
  = fst <$> refreshArgsSub t


-- NV TODO: this does not refreshes args if they are wrapped in an RRTy
refreshArgsSub :: SpecType -> CG (SpecType, F.Subst)
refreshArgsSub t
  = do ts     <- mapM refreshArgs ts_u
       xs'    <- mapM (\_ -> fresh) xs
       let sus = F.mkSubst <$> (L.inits $ zip xs (F.EVar <$> xs'))
       let su  = last sus
       let ts' = zipWith F.subst sus ts
       let t'  = fromRTypeRep $ trep {ty_binds = xs', ty_args = ts', ty_res = F.subst su tbd}
       return (t', su)
    where
       trep    = toRTypeRep t
       xs      = ty_binds trep
       ts_u    = ty_args  trep
       tbd     = ty_res   trep



-------------------------------------------------------------------------------
----------------------- TERMINATION TYPE --------------------------------------
-------------------------------------------------------------------------------

makeDecrIndex :: (Var, Template SpecType)-> CG [Int]
makeDecrIndex (x, Assumed t)
  = do dindex <- makeDecrIndexTy x t
       case dindex of
         Left _  -> return []
         Right i -> return i
makeDecrIndex (x, Asserted t)
  = do dindex <- makeDecrIndexTy x t
       case dindex of
         Left msg -> addWarning msg >> return []
         Right i  -> return i
makeDecrIndex _ = return []

makeDecrIndexTy x t
  = do spDecr <- specDecr <$> get
       autosz <- autoSize <$> get
       hint   <- checkHint' autosz (L.lookup x $ spDecr)
       case dindex autosz of
         Nothing -> return $ Left msg
         Just i  -> return $ Right $ fromMaybe [i] hint
    where
       ts         = ty_args trep
       checkHint' = \autosz -> checkHint x ts (isDecreasing autosz cenv)
       dindex     = \autosz -> L.findIndex    (isDecreasing autosz cenv) ts
       msg        = ErrTermin [x] (getSrcSpan x) (text "No decreasing parameter")
       cenv       = makeNumEnv ts
       trep       = toRTypeRep $ unOCons t


recType _ ((_, []), (_, [], t))
  = t

recType autoenv ((vs, indexc), (_, index, t))
  = makeRecType autoenv t v dxt index
  where v    = (vs !!)  <$> indexc
        dxt  = (xts !!) <$> index
        xts  = zip (ty_binds trep) (ty_args trep)
        trep = toRTypeRep $ unOCons t

checkIndex (x, vs, t, index)
  = do mapM_ (safeLogIndex msg' vs) index
       mapM  (safeLogIndex msg  ts) index
    where
       loc   = getSrcSpan x
       ts    = ty_args $ toRTypeRep $ unOCons $ unTemplate t
       msg'  = ErrTermin [x] loc (text $ "No decreasing " ++ show index ++ "-th argument on " ++ (showPpr x) ++ " with " ++ (showPpr vs))
       msg   = ErrTermin [x] loc (text "No decreasing parameter")

makeRecType autoenv t vs dxs is
  = mergecondition t $ fromRTypeRep $ trep {ty_binds = xs', ty_args = ts'}
  where
    (xs', ts') = unzip $ replaceN (last is) (makeDecrType autoenv vdxs) xts
    vdxs       = zip vs dxs
    xts        = zip (ty_binds trep) (ty_args trep)
    trep       = toRTypeRep $ unOCons t

unOCons (RAllT v t)        = RAllT v $ unOCons t
unOCons (RAllP p t)        = RAllP p $ unOCons t
unOCons (RFun x tx t r)    = RFun x (unOCons tx) (unOCons t) r
unOCons (RRTy _ _ OCons t) = unOCons t
unOCons t                  = t


mergecondition (RAllT _ t1) (RAllT v t2)
  = RAllT v $ mergecondition t1 t2
mergecondition (RAllP _ t1) (RAllP p t2)
  = RAllP p $ mergecondition t1 t2
mergecondition (RRTy xts r OCons t1) t2
  = RRTy xts r OCons (mergecondition t1 t2)
mergecondition (RFun _ t11 t12 _) (RFun x2 t21 t22 r2)
  = RFun x2 (mergecondition t11 t21) (mergecondition t12 t22) r2
mergecondition _ t
  = t

safeLogIndex err ls n
  | n >= length ls = addWarning err >> return Nothing
  | otherwise      = return $ Just $ ls !! n

checkHint _ _ _ Nothing
  = return Nothing

checkHint x _ _ (Just ns) | L.sort ns /= ns
  = addWarning (ErrTermin [x] loc (text "The hints should be increasing")) >> return Nothing
  where loc = getSrcSpan x

checkHint x ts f (Just ns)
  = (mapM (checkValidHint x ts f) ns) >>= (return . Just . catMaybes)

checkValidHint x ts f n
  | n < 0 || n >= length ts = addWarning err >> return Nothing
  | f (ts L.!! n)           = return $ Just n
  | otherwise               = addWarning err >> return Nothing
  where err = ErrTermin [x] loc (text $ "Invalid Hint " ++ show (n+1) ++ " for " ++ (showPpr x) ++  "\nin\n" ++ show (ts))
        loc = getSrcSpan x

-------------------------------------------------------------------
-------------------- Generation: Corebind -------------------------
-------------------------------------------------------------------
consCBTop :: (Var -> Bool) -> CGEnv -> CoreBind -> CG CGEnv
consCBLet :: CGEnv -> CoreBind -> CG CGEnv
-------------------------------------------------------------------

consCBLet γ cb
  = do oldtcheck <- tcheck <$> get
       strict    <- specLazy <$> get
       let tflag  = oldtcheck
       let isStr  = tcond cb strict
       -- TODO: yuck.
       modify $ \s -> s { tcheck = tflag && isStr }
       γ' <- consCB (tflag && isStr) isStr γ cb
       modify $ \s -> s{tcheck = oldtcheck}
       return γ'

consCBTop trustBinding γ cb | all trustBinding xs
  = do ts <- mapM trueTy (varType <$> xs)
       foldM (\γ xt -> (γ, "derived") += xt) γ (zip xs' ts)
  where xs             = bindersOf cb
        xs'            = F.symbol <$> xs

consCBTop _ γ cb
  = do oldtcheck <- tcheck <$> get
       strict    <- specLazy <$> get
       let tflag  = oldtcheck
       let isStr  = tcond cb strict
       modify $ \s -> s{tcheck = tflag && isStr}
       γ' <- consCB (tflag && isStr) isStr γ cb
       modify $ \s -> s{tcheck = oldtcheck}
       return γ'

tcond cb strict
  = not $ any (\x -> S.member x strict || isInternal x) (binds cb)
  where binds (NonRec x _) = [x]
        binds (Rec xes)    = fst $ unzip xes

-------------------------------------------------------------------
consCB :: Bool -> Bool -> CGEnv -> CoreBind -> CG CGEnv
-------------------------------------------------------------------

consCBSizedTys γ xes
  = do xets''    <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       sflag     <- scheck <$> get
       autoenv   <- autoSize <$> get
       let cmakeFinType = if sflag then makeFinType else id
       let cmakeFinTy   = if sflag then makeFinTy   else snd
       let xets = mapThd3 (fmap cmakeFinType) <$> xets''
       ts'      <- mapM (T.mapM refreshArgs) $ (thd3 <$> xets)
       let vs    = zipWith collectArgs ts' es
       is       <- mapM makeDecrIndex (zip xs ts') >>= checkSameLens
       let ts = cmakeFinTy  <$> zip is ts'
       let xeets = (\vis -> [(vis, x) | x <- zip3 xs is $ map unTemplate ts]) <$> (zip vs is)
       (L.transpose <$> mapM checkIndex (zip4 xs vs ts is)) >>= checkEqTypes
       let rts   = (recType autoenv <$>) <$> xeets
       let xts   = zip xs ts
       γ'       <- foldM extender γ xts
       let γs    = [γ' `withTRec` (zip xs rts') | rts' <- rts]
       let xets' = zip3 xs es ts
       mapM_ (uncurry $ consBind True) (zip γs xets')
       return γ'
  where
       (xs, es) = unzip xes
       collectArgs    = collectArguments . length . ty_binds . toRTypeRep . unOCons . unTemplate
       checkEqTypes :: [[Maybe SpecType]] -> CG [[SpecType]]
       checkEqTypes x = mapM (checkAll err1 toRSort) (catMaybes <$> x)
       checkSameLens  = checkAll err2 length
       err1           = ErrTermin xs loc $ text "The decreasing parameters should be of same type"
       err2           = ErrTermin xs loc $ text "All Recursive functions should have the same number of decreasing parameters"
       loc            = getSrcSpan (head xs)

       checkAll _   _ []            = return []
       checkAll err f (x:xs)
         | all (==(f x)) (f <$> xs) = return (x:xs)
         | otherwise                = addWarning err >> return []

consCBWithExprs γ xes
  = do xets'     <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       texprs <- termExprs <$> get
       let xtes = catMaybes $ (`lookup` texprs) <$> xs
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

makeFinTy (ns, t) = fmap go t
  where
    go t = fromRTypeRep $ trep {ty_args = args'}
      where
        trep = toRTypeRep t
        args' = mapNs ns makeFinType $ ty_args trep

makeTermEnvs γ xtes xes ts ts' = withTRec γ . zip xs <$> rts
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
    collectArgs  = collectArguments . length . ty_binds . toRTypeRep
    err x        = "Constant: makeTermEnvs: no terminating expression for " ++ showPpr x

addObligation :: Oblig -> SpecType -> RReft -> SpecType
addObligation o t r  = mkArrow αs πs ls xts $ RRTy [] r o t2
  where
    (αs, πs, ls, t1) = bkUniv t
    (xs, ts, rs, t2) = bkArrow t1
    xts              = zip3 xs ts rs


consCB tflag _ γ (Rec xes) | tflag
  = do texprs <- termExprs <$> get
       modify $ \i -> i { recCount = recCount i + length xes }
       let xxes = catMaybes $ (`lookup` texprs) <$> xs
       if null xxes
         then consCBSizedTys γ xes
         else check xxes <$> consCBWithExprs γ xes
  where xs = fst $ unzip xes
        check ys r | length ys == length xs = r
                   | otherwise              = errorstar err
        err = printf "%s: Termination expressions should be provided for ALL mutual recursive functions" loc
        loc = showPpr $ getSrcSpan (head xs)
        lookup k m | Just x <- M.lookup k m = Just (k, x)
                   | otherwise              = Nothing

consCB _ str γ (Rec xes) | not str
  = do xets'   <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       sflag     <- scheck <$> get
       let cmakeDivType = if sflag then makeDivType else id
       let xets = mapThd3 (fmap cmakeDivType) <$> xets'
       modify $ \i -> i { recCount = recCount i + length xes }
       let xts = [(x, to) | (x, _, to) <- xets]
       γ'     <- foldM extender (γ `withRecs` (fst <$> xts)) xts
       mapM_ (consBind True γ') xets
       return γ'

consCB _ _ γ (Rec xes)
  = do xets   <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       modify $ \i -> i { recCount = recCount i + length xes }
       let xts = [(x, to) | (x, _, to) <- xets]
       γ'     <- foldM extender (γ `withRecs` (fst <$> xts)) xts
       mapM_ (consBind True γ') xets
       return γ'

-- | NV: Dictionaries are not checked, because
-- | class methods' preconditions are not satisfied
consCB _ _ γ (NonRec x _) | isDictionary x
  = do t  <- trueTy (varType x)
       extender γ (x, Assumed t)
  where
    isDictionary = isJust . dlookup (denv γ)


consCB _ _ γ (NonRec x (App (Var w) (Type τ))) | isDictionary w
  = do t      <- trueTy τ
       addW    $ WfC γ t
       let xts = dmap (f t) $ safeFromJust (show w ++ "Not a dictionary"  ) $ dlookup (denv γ) w
       let  γ' = γ{denv = dinsert (denv γ) x xts }
       t      <- trueTy (varType x)
       extender γ' (x, Assumed t)
   where
       f t' (RAllT α te) = subsTyVar_meet' (α, t') te
       f _ _ = error "consCB on Dictionary: this should not happen"
       isDictionary = isJust . dlookup (denv γ)



consCB _ _ γ (NonRec x e)
  = do to  <- varTemplate γ (x, Nothing)
       to' <- consBind False γ (x, e, to) >>= (addPostTemplate γ)
       extender γ (x, to')

consBind isRec γ (x, e, Asserted spect)
  = do let γ'         = (γ `setLoc` getSrcSpan x) `setBind` x
           (_,πs,_,_) = bkUniv spect
       γπ    <- foldM addPToEnv γ' πs
       cconsE γπ e spect
       when (F.symbol x `elemHEnv` holes γ) $
         -- have to add the wf constraint here for HOLEs so we have the proper env
         addW $ WfC γπ $ fmap killSubst spect
       addIdA x (defAnn isRec spect)
       return $ Asserted spect -- Nothing

consBind isRec γ (x, e, Assumed spect)
  = do let γ' = (γ `setLoc` getSrcSpan x) `setBind` x
       γπ    <- foldM addPToEnv γ' πs
       cconsE γπ e =<< true spect
       addIdA x (defAnn isRec spect)
       return $ Asserted spect -- Nothing
  where πs   = ty_preds $ toRTypeRep spect

consBind isRec γ (x, e, Unknown)
  = do t     <- consE (γ `setBind` x) e
       addIdA x (defAnn isRec t)
       return $ Asserted t

noHoles = and . foldReft (\_ r bs -> not (hasHole r) : bs) []

killSubst :: RReft -> RReft
killSubst = fmap killSubstReft

killSubstReft :: F.Reft -> F.Reft
killSubstReft = trans kv () ()
  where
    kv    = defaultVisitor { txPred = ks }
    ks _ (F.PKVar k _) = F.PKVar k mempty
    ks _ p             = p

    -- tx (F.Reft (s, rs)) = F.Reft (s, map f rs)
    -- f (F.RKvar k _)     = F.RKvar k mempty
    -- f (F.RConc p)       = F.RConc p

defAnn True  = AnnRDf
defAnn False = AnnDef

addPToEnv γ π
  = do γπ <- γ ++= ("addSpec1", pname π, pvarRType π)
       foldM (++=) γπ [("addSpec2", x, ofRSort t) | (t, x, _) <- pargs π]

extender γ (x, Asserted t) = γ ++= ("extender", F.symbol x, t)
extender γ (x, Assumed t)  = γ ++= ("extender", F.symbol x, t)
extender γ _               = return γ


data Template a = Asserted a | Assumed a | Unknown deriving (Functor, F.Foldable, T.Traversable)

deriving instance (Show a) => (Show (Template a))

unTemplate (Asserted t) = t
unTemplate (Assumed t) = t
unTemplate _ = errorstar "Constraint.Generate.unTemplate called on `Unknown`"

addPostTemplate γ (Asserted t) = Asserted <$> addPost γ t
addPostTemplate γ (Assumed  t) = Assumed  <$> addPost γ t
addPostTemplate _ Unknown      = return Unknown

safeFromAsserted _ (Asserted t) = t
safeFromAsserted msg _ = errorstar $ "safeFromAsserted:" ++ msg

-- | @varTemplate@ is only called with a `Just e` argument when the `e`
-- corresponds to the body of a @Rec@ binder.
varTemplate :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Template SpecType)
varTemplate γ (x, eo)
  = case (eo, lookupREnv (F.symbol x) (grtys γ), lookupREnv (F.symbol x) (assms γ)) of
      (_, Just t, _) -> Asserted <$> refreshArgsTop (x, t)
      (_, _, Just t) -> Assumed  <$> refreshArgsTop (x, t)
      (Just e, _, _) -> do t  <- freshTy_expr RecBindE e (exprType e)
                           addW (WfC γ t)
                           Asserted <$> refreshArgsTop (x, t)
      (_,      _, _) -> return Unknown

-------------------------------------------------------------------
-------------------- Generation: Expression -----------------------
-------------------------------------------------------------------

----------------------- Type Checking -----------------------------
cconsE :: CGEnv -> Expr Var -> SpecType -> CG ()
-------------------------------------------------------------------
cconsE γ e@(Let b@(NonRec x _) ee) t
  = do sp <- specLVars <$> get
       if (x `S.member` sp) || isDefLazyVar x
        then cconsLazyLet γ e t
        else do γ'  <- consCBLet γ b
                cconsE γ' ee t
  where
       isDefLazyVar = L.isPrefixOf "fail" . showPpr

cconsE γ e (RAllP p t)
  = cconsE γ' e t''
  where
    t'         = replacePredsWithRefs su <$> t
    su         = (uPVar p, pVartoRConc p)
    (css, t'') = splitConstraints t'
    γ'         = L.foldl' addConstraints γ css

cconsE γ (Let b e) t
  = do γ'  <- consCBLet γ b
       cconsE γ' e t

cconsE γ (Case e x _ cases) t
  = do γ'  <- consCBLet γ (NonRec x e)
       forM_ cases $ cconsCase γ' x t nonDefAlts
    where
       nonDefAlts = [a | (a, _, _) <- cases, a /= DEFAULT]

cconsE γ (Lam α e) (RAllT _ t) | isKindVar α
  = cconsE γ e t

cconsE γ (Lam α e) (RAllT α' t) | isTyVar α
  = cconsE γ e $ subsTyVar_meet' (α', rVar α) t

cconsE γ (Lam x e) (RFun y ty t _)
  | not (isTyVar x)
  = do γ' <- (γ, "cconsE") += (F.symbol x, ty)
       cconsE γ' e (t `F.subst1` (y, F.EVar $ F.symbol x))
       addIdA x (AnnDef ty)

cconsE γ (Tick tt e) t
  = cconsE (γ `setLoc` tickSrcSpan tt) e t

-- GHC 7.10 encodes type classes with a single method as newtypes and
-- `cast`s between the method and class type instead of applying the
-- class constructor. Just rewrite the core to what we're used to
-- seeing..
cconsE γ (Cast e co) t
  | Pair _t1 t2 <- coercionKind co
  , isClassPred t2
  , (tc,ts) <- splitTyConApp t2
  , [dc]   <- tyConDataCons tc
  = cconsE γ (mkCoreConApps dc $ map Type ts ++ [e]) t

cconsE γ e@(Cast e' _) t
  = do t' <- castTy γ (exprType e) e'
       addC (SubC γ t' t) ("cconsE Cast" ++ showPpr e)

cconsE γ e t
  = do te  <- consE γ e
       te' <- instantiatePreds γ e te >>= addPost γ
       addC (SubC γ te' t) ("cconsE" ++ showPpr e)


splitConstraints (RRTy cs _ OCons t)
  = let (css, t') = splitConstraints t in (cs:css, t')
splitConstraints (RFun x tx@(RApp c _ _ _) t r) | isClass c
  = let (css, t') = splitConstraints t in (css, RFun x tx t' r)
splitConstraints t
  = ([], t)

-------------------------------------------------------------------
-- | @instantiatePreds@ peels away the universally quantified @PVars@
--   of a @RType@, generates fresh @Ref@ for them and substitutes them
--   in the body.
-------------------------------------------------------------------
instantiatePreds γ e (RAllP π t)
  = do r     <- freshPredRef γ e π
       instantiatePreds γ e $ replacePreds "consE" t [(π, r)]

instantiatePreds _ _ t0
  = return t0

-------------------------------------------------------------------
-- | @instantiateStrata@ generates fresh @Strata@ vars and substitutes
--   them inside the body of the type.
-------------------------------------------------------------------

instantiateStrata ls t = substStrata t ls <$> mapM (\_ -> fresh) ls

substStrata t ls ls'   = F.substa f t
  where
    f x                = fromMaybe x $ L.lookup x su
    su                 = zip ls ls'

-------------------------------------------------------------------
cconsLazyLet γ (Let (NonRec x ex) e) t
  = do tx <- trueTy (varType x)
       γ' <- (γ, "Let NonRec") +++= (x', ex, tx)
       cconsE γ' e t
    where
       x' = F.symbol x

cconsLazyLet _ _ _
  = errorstar "Constraint.Generate.cconsLazyLet called on invalid inputs"

--------------------------------------------------------------------------------
-- | Type Synthesis ------------------------------------------------------------
--------------------------------------------------------------------------------
consE :: CGEnv -> Expr Var -> CG SpecType
--------------------------------------------------------------------------------

consE γ (Var x)
  = do t <- varRefType γ x
       addLocA (Just x) (loc γ) (varAnn γ x t)
       return t

consE _ (Lit c)
  = refreshVV $ uRType $ literalFRefType c

consE γ (App e (Type τ)) | isKind τ
  = consE γ e


consE γ e'@(App e (Type τ))
  = do RAllT α te <- checkAll ("Non-all TyApp with expr", e) <$> consE γ e
       t          <- if isGeneric α te then freshTy_type TypeInstE e τ else trueTy τ
       addW        $ WfC γ t
       t'         <- refreshVV t
       instantiatePreds γ e' $ subsTyVar_meet' (α, t') te

consE γ e'@(App e a) | isDictionary a
  = if isJust tt
      then return $ fromJust tt
      else do ([], πs, ls, te) <- bkUniv <$> consE γ e
              te0              <- instantiatePreds γ e' $ foldr RAllP te πs
              te'              <- instantiateStrata ls te0
              (γ', te''')      <- dropExists γ te'
              te''             <- dropConstraints γ te'''
              updateLocA {- πs -}  (exprLoc e) te''
              let RFun x tx t _ = checkFun ("Non-fun App with caller ", e') te''
              pushConsBind      $ cconsE γ' a tx
              addPost γ'        $ maybe (checkUnbound γ' e' x t a) (F.subst1 t . (x,)) (argExpr γ a)
  where
    grepfunname (App x (Type _)) = grepfunname x
    grepfunname (Var x)          = x
    grepfunname e                = errorstar $ "grepfunname on \t" ++ showPpr e
    mdict w                      = case w of
                                     Var x    -> case dlookup (denv γ) x of {Just _ -> Just x; Nothing -> Nothing}
                                     Tick _ e -> mdict e
                                     _        -> Nothing
    isDictionary _               = isJust (mdict a)
    d = fromJust (mdict a)
    dinfo = dlookup (denv γ) d
    tt = dhasinfo dinfo $ grepfunname e



consE γ e'@(App e a)
  = do ([], πs, ls, te) <- bkUniv <$> consE γ e
       te0              <- instantiatePreds γ e' $ foldr RAllP te πs
       te'              <- instantiateStrata ls te0
       (γ', te''')      <- dropExists γ te'
       te''             <- dropConstraints γ te'''
       updateLocA {- πs -}  (exprLoc e) te''
       let RFun x tx t _ = checkFun ("Non-fun App with caller ", e') te''
       pushConsBind      $ cconsE γ' a tx
       addPost γ'        $ maybe (checkUnbound γ' e' x t a) (F.subst1 t . (x,)) (argExpr γ a)

consE γ (Lam α e) | isTyVar α
  = liftM (RAllT (rTyVar α)) (consE γ e)

consE γ  e@(Lam x e1)
  = do tx      <- freshTy_type LamE (Var x) τx
       γ'      <- ((γ, "consE") += (F.symbol x, tx))
       t1      <- consE γ' e1
       addIdA x $ AnnDef tx
       addW     $ WfC γ tx
       return   $ rFun (F.symbol x) tx t1
    where
      FunTy τx _ = exprType e

-- EXISTS-BASED CONSTRAINTS HEREHEREHEREHERE
-- Currently suppressed because they break all sorts of invariants,
-- e.g. for `unfoldR`...
-- consE γ e@(Let b@(NonRec x _) e')
--   = do γ'    <- consCBLet γ b
--        consElimE γ' [F.symbol x] e'
--
-- consE γ (Case e x _ [(ac, ys, ce)])
--   = do γ'  <- consCBLet γ (NonRec x e)
--        γ'' <- caseEnv γ' x [] ac ys
--        consElimE γ'' (F.symbol <$> (x:ys)) ce

consE γ e@(Let _ _)
  = cconsFreshE LetE γ e

consE γ e@(Case _ _ _ _)
  = cconsFreshE CaseE γ e

consE γ (Tick tt e)
  = do t <- consE (γ `setLoc` l) e
       addLocA Nothing l (AnnUse t)
       return t
    where l = tickSrcSpan tt

-- GHC 7.10 encodes type classes with a single method as newtypes and
-- `cast`s between the method and class type instead of applying the
-- class constructor. Just rewrite the core to what we're used to
-- seeing..
consE γ (Cast e co)
  | Pair _t1 t2 <- coercionKind co
  , isClassPred t2
  , (tc,ts) <- splitTyConApp t2
  , [dc]   <- tyConDataCons tc
  = consE γ (mkCoreConApps dc $ map Type ts ++ [e])

consE γ e@(Cast e' _)
  = castTy γ (exprType e) e'

consE _ e@(Coercion _)
   = trueTy $ exprType e

consE _ e@(Type t)
  = errorstar $ "consE cannot handle type " ++ showPpr (e, t)

castTy _ τ (Var x)
  = do t <- trueTy τ
       return $  t `strengthen` (uTop $ F.uexprReft $ F.expr x)

castTy g t (Tick _ e)
  = castTy g t e

castTy _ _ e
  = errorstar $ "castTy cannot handle expr " ++ showPpr e


singletonReft = uTop . F.symbolReft . F.symbol

-- | @consElimE@ is used to *synthesize* types by **existential elimination**
--   instead of *checking* via a fresh template. That is, assuming
--      γ |- e1 ~> t1
--   we have
--      γ |- let x = e1 in e2 ~> Ex x t1 t2
--   where
--      γ, x:t1 |- e2 ~> t2
--   instead of the earlier case where we generate a fresh template `t` and check
--      γ, x:t1 |- e <~ t

-- consElimE γ xs e
--   = do t     <- consE γ e
--        xts   <- forM xs $ \x -> (x,) <$> (γ ??= x)
--        return $ rEx xts t

-- | @consFreshE@ is used to *synthesize* types with a **fresh template** when
--   the above existential elimination is not easy (e.g. at joins, recursive binders)

cconsFreshE kvkind γ e
  = do t   <- freshTy_type kvkind e $ exprType e
       addW $ WfC γ t
       cconsE γ e t
       return t

checkUnbound γ e x t a
  | x `notElem` (F.syms t)
  = t
  | otherwise
  = errorstar $ "checkUnbound: " ++ show x ++ " is elem of syms of " ++ show t
                 ++ "\nIn\t"  ++ showPpr e ++ " at " ++ showPpr (loc γ) ++ "\nArg = \n" ++ show a

dropExists γ (REx x tx t) = liftM (, t) $ (γ, "dropExists") += (x, tx)
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
  = do cγ <- caseEnv γ x acs ac ys
       cconsE cγ ce t

--------------------------------------------------------------------------------
refreshTy :: SpecType -> CG SpecType
--------------------------------------------------------------------------------
refreshTy t = refreshVV t >>= refreshArgs

refreshVV (RAllT a t) = liftM (RAllT a) (refreshVV t)
refreshVV (RAllP p t) = liftM (RAllP p) (refreshVV t)

refreshVV (REx x t1 t2)
  = do [t1', t2'] <- mapM refreshVV [t1, t2]
       liftM (shiftVV (REx x t1' t2')) fresh

refreshVV (RFun x t1 t2 r)
  = do [t1', t2'] <- mapM refreshVV [t1, t2]
       liftM (shiftVV (RFun x t1' t2' r)) fresh

refreshVV (RAppTy t1 t2 r)
  = do [t1', t2'] <- mapM refreshVV [t1, t2]
       liftM (shiftVV (RAppTy t1' t2' r)) fresh

refreshVV (RApp c ts rs r)
  = do ts' <- mapM refreshVV ts
       rs' <- mapM refreshVVRef rs
       liftM (shiftVV (RApp c ts' rs' r)) fresh

refreshVV t
  = return t

refreshVVRef (RProp ss (RHole r))
  = return $ RProp ss (RHole r)

refreshVVRef (RProp ss t)
  = do xs    <- mapM (\_ -> fresh) (fst <$> ss)
       let su = F.mkSubst $ zip (fst <$> ss) (F.EVar <$> xs)
       liftM (RProp (zip xs (snd <$> ss)) . F.subst su) (refreshVV t)




-------------------------------------------------------------------------------------
caseEnv   :: CGEnv -> Var -> [AltCon] -> AltCon -> [Var] -> CG CGEnv
-------------------------------------------------------------------------------------
caseEnv γ x _   (DataAlt c) ys
  = do let (x' : ys')    = F.symbol <$> (x:ys)
       xt0              <- checkTyCon ("checkTycon cconsCase", x) <$> γ ??= x
       let xt            = shiftVV xt0 x'
       tdc              <- γ ??= ({- F.symbol -} dataConWorkId c) >>= refreshVV
       let (rtd, yts, _) = unfoldR tdc xt ys
       let r1            = dataConReft   c   ys'
       let r2            = dataConMsReft rtd ys'
       let xt            = (xt0 `F.meet` rtd) `strengthen` (uTop (r1 `F.meet` r2))
       let cbs           = safeZip "cconsCase" (x':ys') (xt0:yts)
       cγ'              <- addBinders γ x' cbs
       cγ               <- addBinders cγ' x' [(x', xt)]
       return cγ

caseEnv γ x acs a _
  = do let x'  = F.symbol x
       xt'    <- (`strengthen` uTop (altReft γ acs a)) <$> (γ ??= x)
       cγ     <- addBinders γ x' [(x', xt')]
       return cγ

altReft _ _ (LitAlt l)   = literalFReft l
altReft γ acs DEFAULT    = mconcat [notLiteralReft l | LitAlt l <- acs]
  where notLiteralReft   = maybe mempty F.notExprReft . snd . literalConst (emb γ)
altReft _ _ _            = error "Constraint : altReft"

unfoldR td (RApp _ ts rs _) ys = (t3, tvys ++ yts, ignoreOblig rt)
  where
        tbody              = instantiatePvs (instantiateTys td ts) $ reverse rs
        (ys0, yts', _, rt) = safeBkArrow $ instantiateTys tbody tvs'
        yts''              = zipWith F.subst sus (yts'++[rt])
        (t3,yts)           = (last yts'', init yts'')
        sus                = F.mkSubst <$> (L.inits [(x, F.EVar y) | (x, y) <- zip ys0 ys'])
        (αs, ys')          = mapSnd (F.symbol <$>) $ L.partition isTyVar ys
        tvs'               = rVar <$> αs
        tvys               = ofType . varType <$> αs

unfoldR _  _                _  = error "Constraint.hs : unfoldR"

instantiateTys = L.foldl' go
  where go (RAllT α tbody) t = subsTyVar_meet' (α, t) tbody
        go _ _               = errorstar "Constraint.instanctiateTy"

instantiatePvs = L.foldl' go
  where go (RAllP p tbody) r = replacePreds "instantiatePv" tbody [(p, r)]
        go _ _               = errorstar "Constraint.instanctiatePv"

checkTyCon _ t@(RApp _ _ _ _) = t
checkTyCon x t                = checkErr x t --errorstar $ showPpr x ++ "type: " ++ showPpr t

checkFun _ t@(RFun _ _ _ _)   = t
checkFun x t                  = checkErr x t

checkAll _ t@(RAllT _ _)      = t
checkAll x t                  = checkErr x t

checkErr (msg, e) t          = errorstar $ msg ++ showPpr e ++ ", type: " ++ showpp t

varAnn γ x t
  | x `S.member` recs γ
  = AnnLoc (getSrcSpan' x)
  | otherwise
  = AnnUse t

getSrcSpan' x
  | loc == noSrcSpan
  = loc
  | otherwise
  = loc
  where loc = getSrcSpan x

-----------------------------------------------------------------------
-- | Helpers: Creating Fresh Refinement -------------------------------
-----------------------------------------------------------------------

freshPredRef :: CGEnv -> CoreExpr -> PVar RSort -> CG SpecProp
freshPredRef γ e (PV _ (PVProp τ) _ as)
  = do t    <- freshTy_type PredInstE e (toType τ)
       args <- mapM (\_ -> fresh) as
       let targs = [(x, s) | (x, (s, y, z)) <- zip args as, (F.EVar y) == z ]
       γ' <- foldM (++=) γ [("freshPredRef", x, ofRSort τ) | (x, τ) <- targs]
       addW $ WfC γ' t
       return $ RProp targs t

freshPredRef _ _ (PV _ PVHProp _ _)
  = errorstar "TODO:EFFECTS:freshPredRef"

--------------------------------------------------------------------------------
-- | Helpers: Creating Refinement Types For Various Things ---------------------
--------------------------------------------------------------------------------

argExpr :: CGEnv -> CoreExpr -> Maybe F.Expr
argExpr _ (Var vy)    = Just $ F.eVar vy
argExpr γ (Lit c)     = snd  $ literalConst (emb γ) c
argExpr γ (Tick _ e)  = argExpr γ e
argExpr _ e           = errorstar $ "argExpr: " ++ showPpr e


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
varRefType γ x = varRefType' γ x <$> (γ ??= x)


varRefType' :: CGEnv -> Var -> SpecType -> SpecType
varRefType' γ x t'
  | Just tys <- trec γ, Just tr  <- M.lookup x' tys
  = tr `strengthenS` xr
  | otherwise
  = t' `strengthenS` xr
  where
    xr = singletonReft x
    x' = F.symbol x

-- | RJ: `nomeet` replaces `strengthenS` for `strengthen` in the definition
--   of `varRefType`. Why does `tests/neg/strata.hs` fail EVEN if I just replace
--   the `otherwise` case? The fq file holds no answers, both are sat.
strengthenS :: (F.Reftable r) => RType c tv r -> r -> RType c tv r
strengthenS (RApp c ts rs r) r'  = RApp c ts rs $ topMeet r r'
strengthenS (RVar a r) r'        = RVar a       $ topMeet r r'
strengthenS (RFun b t1 t2 r) r'  = RFun b t1 t2 $ topMeet r r'
strengthenS (RAppTy t1 t2 r) r'  = RAppTy t1 t2 $ topMeet r r'
strengthenS t _                  = t
topMeet r r' = F.top r `F.meet` r'


--------------------------------------------------------------------------------
-- | Cleaner Signatures For Rec-bindings ---------------------------------------
--------------------------------------------------------------------------------

exprLoc                         :: CoreExpr -> Maybe SrcSpan

exprLoc (Tick tt _)             = Just $ tickSrcSpan tt
exprLoc (App e a) | isType a    = exprLoc e
exprLoc _                       = Nothing

isType (Type _)                 = True
isType a                        = eqType (exprType a) predType


exprRefType :: CoreExpr -> SpecType
exprRefType = exprRefType_ M.empty

exprRefType_ :: M.HashMap Var SpecType -> CoreExpr -> SpecType
exprRefType_ γ (Let b e)
  = exprRefType_ (bindRefType_ γ b) e

exprRefType_ γ (Lam α e) | isTyVar α
  = RAllT (rTyVar α) (exprRefType_ γ e)

exprRefType_ γ (Lam x e)
  = rFun (F.symbol x) (ofType $ varType x) (exprRefType_ γ e)

exprRefType_ γ (Tick _ e)
  = exprRefType_ γ e

exprRefType_ γ (Var x)
  = M.lookupDefault (ofType $ varType x) x γ

exprRefType_ _ e
  = ofType $ exprType e

bindRefType_ γ (Rec xes)
  = extendγ γ [(x, exprRefType_ γ e) | (x,e) <- xes]

bindRefType_ γ (NonRec x e)
  = extendγ γ [(x, exprRefType_ γ e)]

extendγ γ xts
  = foldr (\(x,t) m -> M.insert x t m) γ xts


isGeneric :: RTyVar -> SpecType -> Bool
isGeneric α t =  all (\(c, α') -> (α'/=α) || isOrd c || isEq c ) (classConstrs t)
  where classConstrs t = [(c, α') | (c, ts) <- tyClasses t
                                  , t'      <- ts
                                  , α'      <- freeTyVars t']
        isOrd          = (ordClassName ==) . className
        isEq           = (eqClassName ==) . className
