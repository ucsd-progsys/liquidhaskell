{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}

-- | This module defines the representation of Subtyping and WF Constraints,
--   and the code for syntax-directed constraint generation.

module Language.Haskell.Liquid.Constraint.Init (
    initEnv ,
    initCGI,
    makeAxiomEnvironment,

    -- NV TODO move getEqBody in a new file
    getEqBody

    ) where

import           Prelude                                       hiding (error, undefined)
import           Coercion
import           DataCon
import           CoreSyn
import           Type
import           TyCon
import           Var
import           Id                                           -- hiding (isExportedId)
import           IdInfo
import           Name        hiding (varName)
import           Control.Monad.State
import           Data.Maybe                                    (isNothing, fromMaybe, catMaybes)
import qualified Data.HashMap.Strict                           as M
import qualified Data.HashSet                                  as S
import qualified Data.List                                     as L
import           Data.Bifunctor
import qualified Language.Fixpoint.Types                       as F
import           Language.Fixpoint.Solver.Instantiate

import           Language.Haskell.Liquid.UX.Config (terminationCheck, allowLiquidInstationationGlobal, allowLiquidInstationationLocal,
                                                    allowRewrite, allowArithmetic)
import qualified Language.Haskell.Liquid.UX.CTags              as Tg
import           Language.Haskell.Liquid.Constraint.Fresh
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.WiredIn               (dictionaryVar)
import qualified Language.Haskell.Liquid.GHC.SpanStack         as Sp
import           Language.Haskell.Liquid.GHC.Interface         (isExportedVar)
import           Language.Haskell.Liquid.Types                 hiding (binds, Loc, loc, freeTyVars, Def)
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.Visitors        hiding (freeVars)
import           Language.Haskell.Liquid.Types.Meet
import           Language.Haskell.Liquid.GHC.Misc             ( dropModuleNames, simplesymbol, hasBaseTypeVar, isDataConId )
import           Language.Haskell.Liquid.Misc
import           Language.Fixpoint.Misc
import           Language.Haskell.Liquid.Types.Literals
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.ToFixpoint (fixConfig)
import           Language.Fixpoint.Smt.Interface (makeSmtContext, smtPush)

import System.IO.Unsafe

-- import Debug.Trace (trace)

--------------------------------------------------------------------------------
initEnv :: GhcInfo -> CG CGEnv
--------------------------------------------------------------------------------
initEnv info
  = do let tce   = gsTcEmbeds sp
       let fVars = impVars info
       let dcs   = filter isConLikeId (snd <$> gsFreeSyms sp)
       let dcs'  = filter isConLikeId fVars
       defaults <- forM fVars $ \x -> liftM (x,) (trueTy $ varType x)
       dcsty    <- forM dcs   makeDataConTypes
       dcsty'   <- forM dcs'  makeDataConTypes
       (hs,f0)  <- refreshHoles $ grty info                  -- asserted refinements     (for defined vars)
       f0''     <- refreshArgs' =<< grtyTop info             -- default TOP reftype      (for exported vars without spec)
       let f0'   = if notruetypes $ getConfig sp then [] else f0''
       f1       <- refreshArgs'   defaults                   -- default TOP reftype      (for all vars)
       f1'      <- refreshArgs' $ makedcs dcsty              -- data constructors
       f2       <- refreshArgs' $ assm info                  -- assumed refinements      (for imported vars)
       f3       <- refreshArgs' $ vals gsAsmSigs sp            -- assumed refinedments     (with `assume`)
       f40      <- refreshArgs' $ vals gsCtors sp              -- constructor refinements  (for measures)
       f5       <- refreshArgs' $ vals gsInSigs sp             -- internal refinements     (from Haskell measures)
       (invs1, f41) <- mapSndM refreshArgs' $ makeAutoDecrDataCons dcsty  (gsAutosize sp) dcs
       (invs2, f42) <- mapSndM refreshArgs' $ makeAutoDecrDataCons dcsty' (gsAutosize sp) dcs'
       let f4    = mergeDataConTypes (mergeDataConTypes f40 (f41 ++ f42)) (filter (isDataConId . fst) f2)
       sflag    <- scheck <$> get
       let senv  = if sflag then f2 else []
       let tx    = mapFst F.symbol . addRInv ialias . strataUnify senv . predsUnify sp
       let bs    = (tx <$> ) <$> [f0 ++ f0', f1 ++ f1', f2, f3, f4, f5]
       modify $ \s -> s{dataConTys = f4}
       lt1s     <- F.toListSEnv . cgLits <$> get
       let lt2s  = [ (F.symbol x, rTypeSort tce t) | (x, t) <- f1' ]
       let tcb   = mapSnd (rTypeSort tce) <$> concat bs
       let γ0    = measEnv sp (head bs) (cbs info) tcb lt1s lt2s (bs!!3) (bs!!5) hs info
       γ  <- globalize <$> foldM (+=) γ0 [("initEnv", x, y) | (x, y) <- concat $ tail bs]
       return γ {invs = is (invs1 ++ invs2)}
  where
    sp           = spec info
    ialias       = mkRTyConIAl $ gsIaliases sp
    vals f       = map (mapSnd val) . f
    mapSndM f    = \(x,y) -> ((x,) <$> f y)
    makedcs      = map strengthenDataConType
    is autoinv   = mkRTyConInv    (gsInvariants sp ++ ((Nothing,) <$> autoinv))

makeDataConTypes :: Var -> CG (Var, SpecType)
makeDataConTypes x = (x,) <$> (trueTy $ varType x)

makeAutoDecrDataCons :: [(Id, SpecType)] -> S.HashSet TyCon -> [Id] -> ([LocSpecType], [(Id, SpecType)])
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

lenOf :: F.Symbol -> F.Expr
lenOf x = F.mkEApp lenLocSymbol [F.EVar x]

makeSizedDataCons :: [(Id, SpecType)] -> DataCon -> Integer -> (RSort, (Id, SpecType))
makeSizedDataCons dcts x' n = (toRSort $ ty_res trep, (x, fromRTypeRep trep{ty_res = tres}))
    where
      x      = dataConWorkId x'
      t      = fromMaybe (impossible Nothing "makeSizedDataCons: this should never happen") $ L.lookup x dcts
      trep   = toRTypeRep t
      tres   = ty_res trep `strengthen` MkUReft (F.Reft (F.vv_, F.PAtom F.Eq (lenOf F.vv_) computelen)) mempty mempty

      recarguments = filter (\(t,_) -> (toRSort t == toRSort tres)) (zip (ty_args trep) (ty_binds trep))
      computelen   = foldr (F.EBin F.Plus) (F.ECon $ F.I n) (lenOf .  snd <$> recarguments)

mergeDataConTypes ::  [(Var, SpecType)] -> [(Var, SpecType)] -> [(Var, SpecType)]
mergeDataConTypes xts yts = merge (L.sortBy f xts) (L.sortBy f yts)
  where
    f (x,_) (y,_) = compare x y
    merge [] ys = ys
    merge xs [] = xs
    merge (xt@(x, tx):xs) (yt@(y, ty):ys)
      | x == y    = (x, mXY x tx y ty) : merge xs ys
      | x <  y    = xt : merge xs (yt : ys)
      | otherwise = yt : merge (xt : xs) ys
    mXY x tx y ty = meetVarTypes (F.pprint x) (getSrcSpan x, tx) (getSrcSpan y, ty)

refreshArgs' :: [(a, SpecType)] -> CG [(a, SpecType)]
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
    tce            = gsTcEmbeds sp
    tyi            = gsTyconEnv sp

--------------------------------------------------------------------------------
measEnv :: GhcSpec
        -> [(F.Symbol, SpecType)]
        -> [CoreBind]
        -> [(F.Symbol, F.Sort)]
        -> [(F.Symbol, F.Sort)]
        -> [(F.Symbol, F.Sort)]
        -> [(F.Symbol, SpecType)]
        -> [(F.Symbol, SpecType)]
        -> [F.Symbol]
        -> GhcInfo
        -> CGEnv
--------------------------------------------------------------------------------
measEnv sp xts cbs _tcb lt1s lt2s asms itys hs info = CGE
  { cgLoc    = Sp.empty
  , renv     = fromListREnv (second val <$> gsMeas sp) []
  , syenv    = F.fromListSEnv $ gsFreeSyms sp
  , litEnv   = F.fromListSEnv lts
  , constEnv = F.fromListSEnv lt2s
  , fenv     = initFEnv $ filterHO (tcb' ++ lts ++ (second (rTypeSort tce . val) <$> gsMeas sp))
  , denv     = gsDicts sp
  , recs     = S.empty
  , fargs    = S.empty
  , invs     = mempty
  , rinvs    = mempty
  , ial      = mkRTyConIAl    $ gsIaliases   sp
  , grtys    = fromListREnv xts  []
  , assms    = fromListREnv asms []
  , intys    = fromListREnv itys []
  , emb      = tce
  , tgEnv    = Tg.makeTagEnv cbs
  , tgKey    = Nothing
  , trec     = Nothing
  , lcb      = M.empty
  , holes    = fromListHEnv hs
  , lcs      = mempty
  , aenv     = axiom_map $ gsLogicMap sp
  , cerr     = Nothing
  , cgInfo   = info
  , cgVar    = Nothing
  }
  where
      tce         = gsTcEmbeds sp
      filterHO xs = if higherOrderFlag sp then xs else filter (F.isFirstOrder . snd) xs
      lts         = lt1s ++ lt2s
      tcb'        = []

assm :: GhcInfo -> [(Var, SpecType)]
assm = assmGrty impVars

grty :: GhcInfo -> [(Var, SpecType)]
grty = assmGrty defVars

assmGrty :: (GhcInfo -> [Var]) -> GhcInfo -> [(Var, SpecType)]
assmGrty f info = [ (x, val t) | (x, t) <- sigs, x `S.member` xs ]
  where
    xs          = S.fromList $ f info
    sigs        = gsTySigs     $ spec info

grtyTop :: GhcInfo -> CG [(Var, SpecType)]
grtyTop info     = forM topVs $ \v -> (v,) <$> trueTy (varType v)
  where
    topVs        = filter isTop $ defVars info
    isTop v      = isExportedVar info v && not (v `S.member` sigVs)
    sigVs        = S.fromList [v | (v,_) <- gsTySigs (spec info) ++ gsAsmSigs (spec info) ++ gsInSigs (spec info)]


infoLits :: (GhcSpec -> [(F.Symbol, LocSpecType)]) -> (F.Sort -> Bool) -> GhcInfo -> F.SEnv F.Sort
infoLits litF selF info = F.fromListSEnv $ cbLits ++ measLits
  where
    cbLits    = filter (selF . snd) $ coreBindLits tce info
    measLits  = filter (selF . snd) $ mkSort <$> litF spc
    spc       = spec info
    tce       = gsTcEmbeds spc
    mkSort    = mapSnd (F.sr_sort . rTypeSortedReft tce . val)

initCGI :: Config -> GhcInfo -> CGInfo
initCGI cfg info = CGInfo {
    fEnv       = F.emptySEnv
  , hsCs       = []
  , sCs        = []
  , hsWfs      = []
  , fixCs      = []
  , isBind     = []
  , fixWfs     = []
  , freshIndex = 0
  , dataConTys = []
  , binds      = F.emptyBindEnv
  , annotMap   = AI M.empty
  , newTyEnv   = M.fromList (mapSnd val <$> gsNewTypes spc)
  , tyConInfo  = tyi
  , tyConEmbed = tce
  , kuts       = mempty
  , kvPacks    = mempty
  , cgLits     = infoLits gsMeas   (const True) info
  , cgConsts   = infoLits gsLits notFn info
  , termExprs  = M.fromList $ gsTexprs spc
  , specDecr   = gsDecr spc
  , specLVars  = gsLvars spc
  , specLazy   = dictionaryVar `S.insert` gsLazy spc
  , tcheck     = terminationCheck cfg
  , scheck     = strata cfg
  , pruneRefs  = pruneUnsorted cfg
  , logErrors  = []
  , kvProf     = emptyKVProf
  , recCount   = 0
  , bindSpans  = M.empty
  , autoSize   = gsAutosize spc
  , allowHO    = higherOrderFlag cfg
  , ghcI       = info
  }
  where
    tce        = gsTcEmbeds spc
    spc        = spec info
    tyi        = gsTyconEnv spc
    notFn      = isNothing . F.functionSort

coreBindLits :: F.TCEmb TyCon -> GhcInfo -> [(F.Symbol, F.Sort)]
coreBindLits tce info
  = sortNub      $ [ (F.symbol x, F.strSort) | (_, Just (F.ESym x)) <- lconsts ]    -- strings
                ++ [ (dconToSym dc, dconToSort dc) | dc <- dcons ]                  -- data constructors
  where
    lconsts      = literalConst tce <$> literals (cbs info)
    dcons        = filter isDCon freeVs
    freeVs       = impVars info ++ (snd <$> gsFreeSyms (spec info))
    dconToSort   = typeSort tce . expandTypeSynonyms . varType
    dconToSym    = F.symbol . idDataCon
    isDCon x     = isDataConId x && not (hasBaseTypeVar x)




makeAxiomEnvironment :: GhcInfo -> [(Var, SpecType)] -> [(Integer, F.SubC Cinfo)] -> AxiomEnv Cinfo
makeAxiomEnvironment info xts fcs
  = AEnv ((axiomName <$> gsAxioms (spec info)) ++ (F.symbol . fst <$> xts))
         (makeEquations info ++ (specTypToEq  <$> xts))
         (concatMap makeSimplify xts)
         fuelMap
         doExpand
         (allowRewrite    cfg)
         (allowArithmetic cfg)
         (debugInstantionation cfg)
         fixCfg
         (makeContext cfg)
  where
    fixCfg = fixConfig fileName cfg

    makeContext cfg = unsafePerformIO $  do
                       ctx <- makeSmtContext (fixConfig fileName cfg) fileName []
                           {-     $ L.nubBy (\(x,_) (y,_) -> x == y)
                                    [(x, toSMT fixCfg fenv s) | (x, s) <- binds', not (M.member x FT.theorySymbols) ] -}
                       smtPush ctx
                       return ctx
    fileName = head (files cfg)  ++ ".evals"
    -- binds'   = {- [(x, s) | (_, x, F.RR s _) <- F.bindEnvToList bds] ++ -} F.toListSEnv fenv

    doExpand = M.fromList $ (\(sid,sub) -> (sid, allowLiquidInstationationGlobal cfg
                || (allowLiquidInstationationLocal cfg
                                      && (maybe False (`M.member` (gsAutoInst (spec info))) (subVar sub)))))
                            <$> fcs

    cfg = getConfig info

    fuelNumber sub = do {v <- subVar sub; lp <- M.lookup v (gsAutoInst (spec info)); lp}

    fuelMap   = M.fromList $ (\(sid, sub) -> (sid, fromMaybe (fuel cfg) (fuelNumber sub))) <$> fcs

    specTypToEq (x, t)
      = Equ (F.symbol x) (ty_binds $ toRTypeRep t)
           (specTypeToResultRef (F.eApps (F.EVar $ F.symbol x) (F.EVar <$> ty_binds (toRTypeRep t))) t)

makeSimplify :: (Var, SpecType) -> [Simplify]
makeSimplify (x, t) = go $ specTypeToResultRef (F.eApps (F.EVar $ F.symbol x) (F.EVar <$> ty_binds (toRTypeRep t))) t
  where
    go (F.PAnd es) = concatMap go es

    go (F.PAtom eq (F.EApp (F.EVar f) dc) bd)
      | eq `elem` [F.Eq, F.Ueq]
      , (F.EVar dc, xs) <- F.splitEApp dc
      , all isEVar xs
      = [SMeasure f dc (fromEVar <$> xs) bd]

    go (F.PIff (F.EApp (F.EVar f) dc) bd)
      | (F.EVar dc, xs) <- F.splitEApp dc
      , all isEVar xs
      = [SMeasure f dc (fromEVar <$> xs) bd]

    go _ = []

    isEVar (F.EVar _) = True
    isEVar _ = False

    fromEVar (F.EVar x) = x
    fromEVar _ = impossible Nothing "makeSimplify.fromEVar"


makeEquations :: GhcInfo -> [Equation]
makeEquations info
  = [ Equ x xs (F.pAnd [makeEqBody x xs e, makeRefBody x xs (lookupSpecType x (gsTySigs $ spec info))]) | AxiomEq x xs e _ <- gsAxioms (spec info)]
  where
    makeEqBody x xs e = F.PAtom F.Eq (F.eApps (F.EVar x) (F.EVar <$> xs)) e
    lookupSpecType x xts = L.lookup x ((mapFst (dropModuleNames . simplesymbol)) <$> xts)
    makeRefBody _ _  Nothing  = F.PTrue
    makeRefBody x xs (Just t) = specTypeToLogic (F.EVar <$> xs) (F.eApps (F.EVar x) (F.EVar <$> xs)) (val t)


getEqBody :: Equation -> Maybe F.Expr
getEqBody (Equ  x xs (F.PAnd ((F.PAtom F.Eq fxs e):_)))
  | (F.EVar f, es) <- F.splitEApp fxs
  , f == x
  , es == (F.EVar <$> xs)
  = Just e
getEqBody _
  = Nothing

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
