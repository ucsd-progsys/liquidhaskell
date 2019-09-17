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
    ) where

import           Prelude                                       hiding (error, undefined)
import           Coercion
import           DataCon
import           CoreSyn
import           Type
import           TyCon
import           Var
import           Id                                           -- hiding (isExportedId)
-- import           IdInfo
import           Name        hiding (varName)
import           Control.Monad.State
import           Data.Maybe                                    (isNothing, fromMaybe, catMaybes)
import qualified Data.HashMap.Strict                           as M
import qualified Data.HashSet                                  as S
import qualified Data.List                                     as L
import           Data.Bifunctor
import qualified Language.Fixpoint.Types                       as F

import           Language.Haskell.Liquid.UX.Config (terminationCheck)
import qualified Language.Haskell.Liquid.UX.CTags              as Tg
import           Language.Haskell.Liquid.Constraint.Fresh
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.WiredIn               (dictionaryVar)
import qualified Language.Haskell.Liquid.GHC.SpanStack         as Sp
-- import           Language.Haskell.Liquid.GHC.Interface         (isExportedVar)
import           Language.Haskell.Liquid.Types                 hiding (binds, Loc, loc, freeTyVars, Def)
-- import           Language.Haskell.Liquid.Types.Names
-- import           Language.Haskell.Liquid.Types.RefType
-- import           Language.Haskell.Liquid.Types.Visitors        hiding (freeVars)
-- import           Language.Haskell.Liquid.Types.Meet
-- import           Language.Haskell.Liquid.Types.Literals
import           Language.Haskell.Liquid.GHC.Misc             ( idDataConM, hasBaseTypeVar, isDataConId) -- dropModuleNames, simplesymbol)
import           Language.Haskell.Liquid.Misc
import           Language.Fixpoint.Misc
import           Language.Haskell.Liquid.Constraint.Types

-- import Debug.Trace (trace)

--------------------------------------------------------------------------------
initEnv :: GhcInfo -> CG CGEnv
--------------------------------------------------------------------------------
initEnv info
  = do let tce   = gsTcEmbeds (gsName sp)
       let fVars = giImpVars (giSrc info)
       let dcs   = filter isConLikeId (snd <$> gsFreeSyms (gsName sp))
       let dcs'  = filter isConLikeId fVars
       defaults <- forM fVars $ \x -> liftM (x,) (trueTy $ varType x)
       dcsty    <- forM dcs   makeDataConTypes
       dcsty'   <- forM dcs'  makeDataConTypes
       (hs,f0)  <- refreshHoles $ grty info                           -- asserted refinements     (for defined vars)
       f0''     <- refreshArgs' =<< grtyTop info                      -- default TOP reftype      (for exported vars without spec)
       let f0'   = if notruetypes $ getConfig sp then [] else f0''
       f1       <- refreshArgs'   defaults                            -- default TOP reftype      (for all vars)
       f1'      <- refreshArgs' $ makeExactDc dcsty                   -- data constructors
       f2       <- refreshArgs' $ assm info                           -- assumed refinements      (for imported vars)
       f3'      <- refreshArgs' =<< recSelectorsTy info                      -- assumed refinements      (for record selectors)
       f3       <- refreshArgs' $ vals gsAsmSigs (gsSig sp)                  -- assumed refinedments     (with `assume`)
       f40      <- makeExactDc <$> (refreshArgs' $ vals gsCtors (gsData sp)) -- constructor refinements  (for measures)
       f5       <- refreshArgs' $ vals gsInSigs (gsSig sp)                   -- internal refinements     (from Haskell measures)
       fi       <- refreshArgs' $ catMaybes $ [(x,) . val <$> getMethodType mt | (x, mt) <- gsMethods $ gsSig $ giSpec info ]
       (invs1, f41) <- mapSndM refreshArgs' $ makeAutoDecrDataCons dcsty  (gsAutosize (gsTerm sp)) dcs
       (invs2, f42) <- mapSndM refreshArgs' $ makeAutoDecrDataCons dcsty' (gsAutosize (gsTerm sp)) dcs'
       let f4    = mergeDataConTypes tce (mergeDataConTypes tce f40 (f41 ++ f42)) (filter (isDataConId . fst) f2)
       sflag    <- scheck <$> get
       let senv  = if sflag then f2 else []
       let tx    = mapFst F.symbol . addRInv ialias . strataUnify senv . predsUnify sp
       let bs    = (tx <$> ) <$> [f0 ++ f0' ++ fi, f1 ++ f1', f2, f3 ++ f3', f4, f5]
       modify $ \s -> s { dataConTys = f4 }
       lt1s     <- F.toListSEnv . cgLits <$> get
       let lt2s  = [ (F.symbol x, rTypeSort tce t) | (x, t) <- f1' ]
       let tcb   = mapSnd (rTypeSort tce) <$> concat bs
       let cbs   = giCbs . giSrc $ info
       let γ0    = measEnv sp (head bs) cbs tcb lt1s lt2s (bs!!3) (bs!!5) hs info
       γ  <- globalize <$> foldM (+=) γ0 ( [("initEnv", x, y) | (x, y) <- concat $ tail bs])
       return γ {invs = is (invs1 ++ invs2)}
  where
    sp           = giSpec info
    ialias       = mkRTyConIAl (gsIaliases (gsData sp))
    vals f       = map (mapSnd val) . f
    mapSndM f    = \(x,y) -> ((x,) <$> f y)
    makeExactDc dcs = if exactDCFlag info then map strengthenDataConType dcs else dcs
    is autoinv   = mkRTyConInv    (gsInvariants (gsData sp) ++ ((Nothing,) <$> autoinv))

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

    simplify invs = dummyLoc . (`strengthen` invariant) .  fmap (\_ -> mempty) <$> L.nub invs
    invariant = MkUReft (F.Reft (F.vv_, F.PAtom F.Ge (lenOf F.vv_) (F.ECon $ F.I 0)) ) mempty mempty

idTyCon :: Id -> Maybe TyCon
idTyCon = fmap dataConTyCon . idDataConM

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

mergeDataConTypes ::  F.TCEmb TyCon -> [(Var, SpecType)] -> [(Var, SpecType)] -> [(Var, SpecType)]
mergeDataConTypes tce xts yts = merge (L.sortBy f xts) (L.sortBy f yts)
  where
    f (x,_) (y,_) = compare x y
    merge [] ys = ys
    merge xs [] = xs
    merge (xt@(x, tx):xs) (yt@(y, ty):ys)
      | x == y    = (x, mXY x tx y ty) : merge xs ys
      | x <  y    = xt : merge xs (yt : ys)
      | otherwise = yt : merge (xt : xs) ys
    mXY x tx y ty = meetVarTypes tce (F.pprint x) (getSrcSpan x, tx) (getSrcSpan y, ty)

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
    tce            = gsTcEmbeds (gsName sp)
    tyi            = gsTyconEnv (gsName sp)


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
  , renv     = fromListREnv (second val <$> gsMeas (gsData sp)) []
  , syenv    = F.fromListSEnv (gsFreeSyms (gsName sp))
  , litEnv   = F.fromListSEnv lts
  , constEnv = F.fromListSEnv lt2s
  , fenv     = initFEnv $ filterHO (tcb' ++ lts ++ (second (rTypeSort tce . val) <$> gsMeas (gsData sp)))
  , denv     = dmapty val $ gsDicts (gsSig sp)
  , recs     = S.empty
  , fargs    = S.empty
  , invs     = mempty
  , rinvs    = mempty
  , ial      = mkRTyConIAl (gsIaliases (gsData sp))
  , grtys    = fromListREnv xts  []
  , assms    = fromListREnv asms []
  , intys    = fromListREnv itys []
  , emb      = tce
  , tgEnv    = Tg.makeTagEnv cbs
  , tgKey    = Nothing
  , trec     = Nothing
  , lcb      = M.empty
  , forallcb = M.empty
  , holes    = fromListHEnv hs
  , lcs      = mempty
  , aenv     = axEnv (gsRefl sp)
  , cerr     = Nothing
  , cgInfo   = info
  , cgVar    = Nothing
  }
  where
      tce         = gsTcEmbeds (gsName sp)
      filterHO xs = if higherOrderFlag sp then xs else filter (F.isFirstOrder . snd) xs
      lts         = lt1s ++ lt2s
      tcb'        = []
      axEnv sp    = M.union (M.mapWithKey (fromMaybe . F.symbol) $ lmVarSyms $ gsLogicMap sp)
                            (M.fromList [(v, F.symbol v) | v <- gsReflects sp])


assm :: GhcInfo -> [(Var, SpecType)]
assm = assmGrty (giImpVars . giSrc)

grty :: GhcInfo -> [(Var, SpecType)]
grty = assmGrty (giDefVars . giSrc) 

assmGrty :: (GhcInfo -> [Var]) -> GhcInfo -> [(Var, SpecType)]
assmGrty f info = [ (x, val t) | (x, t) <- sigs, x `S.member` xs ]
  where
    xs          = S.fromList . f             $ info
    sigs        = gsTySigs  . gsSig . giSpec $ info


recSelectorsTy :: GhcInfo -> CG [(Var, SpecType)]
recSelectorsTy info = forM topVs $ \v -> (v,) <$> trueTy (varType v)
  where
    topVs        = filter isTop $ giDefVars (giSrc info)
    isTop v      = isExportedVar (giSrc info) v && not (v `S.member` sigVs) &&  isRecordSelector v
    sigVs        = S.fromList [v | (v,_) <- gsTySigs sp ++ gsAsmSigs sp ++ gsInSigs sp]
    sp           = gsSig . giSpec $ info
    


grtyTop :: GhcInfo -> CG [(Var, SpecType)]
grtyTop info     = forM topVs $ \v -> (v,) <$> trueTy (varType v)
  where
    topVs        = filter isTop $ giDefVars (giSrc info)
    isTop v      = isExportedVar (giSrc info) v && not (v `S.member` sigVs) && not (isRecordSelector v)
    sigVs        = S.fromList [v | (v,_) <- gsTySigs sp ++ gsAsmSigs sp ++ gsInSigs sp]
    sp           = gsSig . giSpec $ info


infoLits :: (GhcSpec -> [(F.Symbol, LocSpecType)]) -> (F.Sort -> Bool) -> GhcInfo -> F.SEnv F.Sort
infoLits litF selF info = F.fromListSEnv $ cbLits ++ measLits
  where
    cbLits    = filter (selF . snd) $ coreBindLits tce info
    measLits  = filter (selF . snd) $ mkSort <$> litF spc
    spc       = giSpec info
    tce       = gsTcEmbeds (gsName spc)
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
  , ebinds     = []
  , annotMap   = AI M.empty
  , holesMap   = M.empty
  , newTyEnv   = M.fromList (mapSnd val <$> gsNewTypes (gsSig spc))
  , tyConInfo  = tyi
  , tyConEmbed = tce
  , kuts       = mempty
  , kvPacks    = mempty
  , cgLits     = infoLits (gsMeas . gsData) (const True) info
  , cgConsts   = infoLits (gsMeas . gsData) notFn        info
  , cgADTs     = gsADTs nspc
  , termExprs  = M.fromList [(v, es) | (v, _, es) <- gsTexprs (gsSig spc) ]
  , specDecr   = gsDecr  tspc
  , specLVars  = gsLvars (gsVars spc)
  , specLazy   = dictionaryVar `S.insert` (gsLazy tspc)
  , specTmVars = gsNonStTerm tspc
  , tcheck     = terminationCheck cfg
  , scheck     = strata cfg
  , pruneRefs  = pruneUnsorted cfg
  , logErrors  = []
  , kvProf     = emptyKVProf
  , recCount   = 0
  , bindSpans  = M.empty
  , autoSize   = gsAutosize tspc
  , allowHO    = higherOrderFlag cfg
  , ghcI       = info
  , unsorted   = F.notracepp "UNSORTED" $ F.makeTemplates $ gsUnsorted $ gsData spc
  }
  where
    tce        = gsTcEmbeds nspc 
    tspc       = gsTerm spc
    spc        = giSpec info
    tyi        = gsTyconEnv nspc
    nspc       = gsName spc
    notFn      = isNothing . F.functionSort

coreBindLits :: F.TCEmb TyCon -> GhcInfo -> [(F.Symbol, F.Sort)]
coreBindLits tce info
  = sortNub      $ [ (F.symbol x, F.strSort) | (_, Just (F.ESym x)) <- lconsts ]    -- strings
                ++ [ (dconToSym dc, dconToSort dc) | dc <- dcons ]                  -- data constructors
  where
    src         = giSrc info
    lconsts      = literalConst tce <$> literals (giCbs src)
    dcons        = filter isDCon freeVs
    freeVs       = giImpVars src ++ freeSyms
    freeSyms     = fmap snd . gsFreeSyms . gsName . giSpec $ info
    dconToSort   = typeSort tce . expandTypeSynonyms . varType
    dconToSym    = F.symbol . idDataCon
    isDCon x     = isDataConId x && not (hasBaseTypeVar x)
