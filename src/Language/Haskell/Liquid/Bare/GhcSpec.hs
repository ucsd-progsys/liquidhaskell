{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ViewPatterns              #-}

module Language.Haskell.Liquid.Bare.GhcSpec (
    GhcSpec(..)
  , makeGhcSpec
  ) where

-- import Debug.Trace (trace)
import           Prelude                                    hiding (error)
import           CoreSyn                                    hiding (Expr)
import qualified CoreSyn
import           HscTypes
import           Id
import           NameSet
import           Name
import           TyCon
import           Var
import           TysWiredIn

import           DataCon                                    (DataCon)
import           InstEnv

import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Bifunctor
import           Data.Maybe


import           Control.Monad.Except                       (catchError)
import           TypeRep                                    (Type(TyConApp))

import           Text.PrettyPrint.HughesPJ (text )

import qualified Control.Exception                          as Ex
import qualified Data.List                                  as L
import qualified Data.HashMap.Strict                        as M
import qualified Data.HashSet                               as S

import           Language.Fixpoint.Misc                     (thd3)
import           Language.Fixpoint.Types                    hiding (Error)

import           Language.Haskell.Liquid.Types.Dictionaries
import           Language.Haskell.Liquid.GHC.Misc           (dropModuleNames, showPpr, getSourcePosE, getSourcePos, sourcePosSrcSpan, isDataConId)
import           Language.Haskell.Liquid.Types.PredType     (makeTyConInfo)
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Misc               (mapSnd)
import           Language.Haskell.Liquid.WiredIn

import qualified Language.Haskell.Liquid.Measure            as Ms

import           Language.Haskell.Liquid.Bare.Check
import           Language.Haskell.Liquid.Bare.DataType
import           Language.Haskell.Liquid.Bare.Env
import           Language.Haskell.Liquid.Bare.Existential
import           Language.Haskell.Liquid.Bare.Measure
import           Language.Haskell.Liquid.Bare.Axiom
import           Language.Haskell.Liquid.Bare.Misc          (makeSymbols, mkVarExpr)
import           Language.Haskell.Liquid.Bare.Plugged
import           Language.Haskell.Liquid.Bare.RTEnv
import           Language.Haskell.Liquid.Bare.Spec
import           Language.Haskell.Liquid.Bare.SymSort
import           Language.Haskell.Liquid.Bare.RefToLogic
import           Language.Haskell.Liquid.Bare.Lookup        (lookupGhcTyCon)

--------------------------------------------------------------------------------
makeGhcSpec :: Config
            -> ModName
            -> [CoreBind]
            -> Maybe [ClsInst]
            -> [Var]
            -> [Var]
            -> NameSet
            -> HscEnv
            -> Either Error LogicMap
            -> [(ModName,Ms.BareSpec)]
            -> IO GhcSpec
--------------------------------------------------------------------------------
makeGhcSpec cfg name cbs instenv vars defVars exports env lmap specs = do
  sp <- throwLeft =<< execBare act initEnv
  let renv = ghcSpecEnv sp
  throwLeft . checkGhcSpec specs renv $ postProcess cbs renv sp
  where
    act       = makeGhcSpec' cfg cbs instenv vars defVars exports specs
    throwLeft = either Ex.throw return
    initEnv   = BE name mempty mempty mempty env lmap' mempty mempty
    lmap'     = case lmap of { Left e -> Ex.throw e; Right x -> x `mappend` listLMap}

listLMap :: LogicMap
listLMap  = toLogicMap [ (nilName , []     , hNil)
                       , (consName, [x, xs], hCons (EVar <$> [x, xs])) ]
  where
    x     = symbol "x"
    xs    = symbol "xs"
    hNil  = mkEApp (dummyLoc $ symbol nilDataCon ) []
    hCons = mkEApp (dummyLoc $ symbol consDataCon)

postProcess :: [CoreBind] -> SEnv SortedReft -> GhcSpec -> GhcSpec
postProcess cbs specEnv sp@(SP {..})
  = sp { tySigs     = tySigs'
       , texprs     = ts
       , asmSigs    = asmSigs'
       , dicts      = dicts'
       , invariants = invs'
       , meas       = meas'
       , inSigs     = inSigs' }
  where
    (sigs, ts')     = replaceLocalBinds allowHO tcEmbeds tyconEnv tySigs texprs specEnv cbs
    (assms, ts'')   = replaceLocalBinds allowHO tcEmbeds tyconEnv asmSigs ts'   specEnv cbs
    (insigs, ts)    = replaceLocalBinds allowHO tcEmbeds tyconEnv inSigs  ts''  specEnv cbs
    tySigs'         = mapSnd (addTyConInfo tcEmbeds tyconEnv <$>) <$> sigs
    asmSigs'        = mapSnd (addTyConInfo tcEmbeds tyconEnv <$>) <$> assms
    inSigs'         = mapSnd (addTyConInfo tcEmbeds tyconEnv <$>) <$> insigs
    dicts'          = dmapty (addTyConInfo tcEmbeds tyconEnv) dicts
    invs'           = mapSnd (addTyConInfo tcEmbeds tyconEnv <$>) <$> invariants
    meas'           = mapSnd (fmap (addTyConInfo tcEmbeds tyconEnv) . txRefSort tyconEnv tcEmbeds) <$> meas
    allowHO         = higherOrderFlag config

ghcSpecEnv :: GhcSpec -> SEnv SortedReft
ghcSpecEnv sp        = fromListSEnv binds
  where
    emb              = tcEmbeds sp
    binds            =  [(x,        rSort t) | (x, Loc _ _ t) <- meas sp]
                     ++ [(symbol v, rSort t) | (v, Loc _ _ t) <- ctors sp]
                     ++ [(x,        vSort v) | (x, v) <- freeSyms sp, isConLikeId v]
    rSort            = rTypeSortedReft emb
    vSort            = rSort . varRSort
    varRSort         :: Var -> RSort
    varRSort         = ofType . varType

------------------------------------------------------------------------------------------------
makeGhcSpec' :: Config -> [CoreBind] -> Maybe [ClsInst] -> [Var] -> [Var] -> NameSet -> [(ModName, Ms.BareSpec)] -> BareM GhcSpec
------------------------------------------------------------------------------------------------
makeGhcSpec' cfg cbs instenv vars defVars exports specs
  = do name          <- modName <$> get
       makeRTEnv  specs
       (tycons, datacons, dcSs, recSs, tyi, embs) <- makeGhcSpecCHOP1 instenv cfg specs
       makeBounds embs name defVars cbs specs
       modify                                   $ \be -> be { tcEnv = tyi }
       (cls, mts)                              <- second mconcat . unzip . mconcat <$> mapM (makeClasses name cfg vars) specs
       (measures, cms', ms', cs', xs')         <- makeGhcSpecCHOP2 cbs specs dcSs datacons cls embs
       (invs, ialias, sigs, asms)              <- makeGhcSpecCHOP3 cfg vars defVars specs name mts embs
       quals   <- mconcat <$> mapM makeQualifiers specs
       syms                                    <- makeSymbols (varInModule name) (vars ++ map fst cs') xs' (sigs ++ asms ++ cs') ms' (map snd invs ++ (snd <$> ialias))
       let su  = mkSubst [ (x, mkVarExpr v) | (x, v) <- syms]
       makeGhcSpec0 cfg defVars exports name (emptySpec cfg)
         >>= makeGhcSpec1 vars defVars embs tyi exports name sigs (recSs ++ asms) cs' ms' cms' su
         >>= makeGhcSpec2 invs ialias measures su
         >>= makeGhcSpec3 (datacons ++ cls) tycons embs syms
         >>= makeSpecDictionaries embs vars specs
         >>= makeGhcAxioms embs cbs name specs
         >>= makeExactDataCons name (exactDC cfg) (snd <$> syms)
         -- This step need the updated logic map, ie should happen after makeGhcAxioms
         >>= makeGhcSpec4 quals defVars specs name su
         >>= addProofType


addProofType :: GhcSpec -> BareM GhcSpec
addProofType spec = do
  tycon <- (Just <$> lookupGhcTyCon (dummyLoc proofTyConName)) `catchError` (\_ -> return Nothing)
  return $ spec { proofType = (`TyConApp` []) <$> tycon }


makeExactDataCons :: ModName -> Bool -> [Var] -> GhcSpec -> BareM GhcSpec
makeExactDataCons n flag vs spec
  | flag      = return $ spec {tySigs = tySigs spec ++ xts}
  | otherwise = return spec
  where
    xts       = makeExact <$> filter f vs
    f v       = isDataConId v && varInModule n v

varInModule :: (Show a, Show a1) => a -> a1 -> Bool
varInModule n v = L.isPrefixOf (show n) $ show v

makeExact :: Var -> (Var, LocSpecType)
makeExact x = (x, dummyLoc . fromRTypeRep $ trep{ty_res = res, ty_binds = xs})
  where
    t    :: SpecType
    t    = ofType $ varType x
    trep = toRTypeRep t
    xs   = zipWith (\_ i -> (symbol ("x" ++ show i))) (ty_args trep) [1..]

    res  = ty_res trep `strengthen` MkUReft ref mempty mempty
    vv   = vv_
    x'   = symbol x --  simpleSymbolVar x
    ref  = Reft (vv, PAtom Eq (EVar vv) eq)
    eq   | null (ty_vars trep) && null xs = EVar x'
         | otherwise = mkEApp (dummyLoc x') (EVar <$> xs)


makeGhcAxioms :: TCEmb TyCon -> [CoreBind] -> ModName -> [(ModName, Ms.BareSpec)] -> GhcSpec -> BareM GhcSpec
makeGhcAxioms tce cbs name bspecs sp = makeAxioms tce cbs sp spec
  where
    spec = fromMaybe mempty $ lookup name bspecs

makeAxioms :: TCEmb TyCon -> [CoreBind] -> GhcSpec -> Ms.BareSpec -> BareM GhcSpec
makeAxioms tce cbs spec sp
  = do lmap          <- logicEnv <$> get
       (ms, tys, as) <- unzip3 <$> mapM (makeAxiom tce lmap cbs spec sp) (S.toList $ Ms.axioms sp)
       lmap'         <- logicEnv <$> get
       return $ spec { meas     = ms         ++  meas   spec
                     , asmSigs  = concat tys ++ asmSigs spec
                     , axioms   = concat as  ++ axioms spec
                     , logicMap = lmap' }

emptySpec     :: Config -> GhcSpec
emptySpec cfg = SP [] [] [] [] [] [] [] [] [] [] mempty [] [] [] [] mempty mempty mempty cfg mempty [] mempty mempty [] mempty Nothing


makeGhcSpec0 :: Config
             -> [Var]
             -> NameSet
             -> ModName
             -> GhcSpec
             -> BareM GhcSpec
makeGhcSpec0 cfg defVars exports name sp
  = do targetVars <- makeTargetVars name defVars $ checks cfg
       return      $ sp { config = cfg
                        , exports = exports
                        , tgtVars = targetVars }

makeGhcSpec1 :: [Var]
             -> [Var]
             -> TCEmb TyCon
             -> M.HashMap TyCon RTyCon
             -> NameSet
             -> ModName
             -> [(Var,Located (RRType RReft))]
             -> [(Var,Located (RRType RReft))]
             -> [(Var,Located (RRType RReft))]
             -> [(Symbol,Located (RRType Reft))]
             -> [(Symbol,Located (RRType Reft))]
             -> Subst
             -> GhcSpec
             -> BareM GhcSpec
makeGhcSpec1 vars defVars embs tyi exports name sigs asms cs' ms' cms' su sp
  = do tySigs      <- makePluggedSigs name embs tyi exports $ tx sigs
       asmSigs     <- makePluggedAsmSigs embs tyi $ tx asms
       ctors       <- makePluggedAsmSigs embs tyi $ tx cs'
       return $ sp { tySigs     = filter (\(v,_) -> v `elem` vs) tySigs
                   , asmSigs    = filter (\(v,_) -> v `elem` vs) asmSigs
                   , ctors      = filter (\(v,_) -> v `elem` vs) ctors
                   , meas       = tx' $ tx $ ms' ++ varMeasures vars ++ cms' }
    where
      tx   = fmap . mapSnd . subst $ su
      tx'  = fmap (mapSnd $ fmap uRType)
      vs   = vars ++ defVars

makeGhcSpec2 :: Monad m
             => [(Maybe Var, LocSpecType)]
             -> [(LocSpecType,LocSpecType)]
             -> MSpec SpecType DataCon
             -> Subst
             -> GhcSpec
             -> m GhcSpec
makeGhcSpec2 invs ialias measures su sp
  = return $ sp { invariants = mapSnd (subst su) <$> invs
                , ialiases   = subst su ialias
                , measures   = subst su
                                 <$> M.elems (Ms.measMap measures)
                                  ++ Ms.imeas measures
                }

makeGhcSpec3 :: [(DataCon, DataConP)] -> [(TyCon, TyConP)] -> TCEmb TyCon -> [(t, Var)] -> GhcSpec -> BareM GhcSpec
makeGhcSpec3 datacons tycons embs syms sp
  = do tcEnv       <- tcEnv    <$> get
       lmap        <- logicEnv <$> get
       inlmap      <- inlines  <$> get
       let dcons'   = mapSnd (txRefToLogic lmap inlmap) <$> datacons
       return  $ sp { tyconEnv   = tcEnv
                    , dconsP     = dcons'
                    , tconsP     = tycons
                    , tcEmbeds   = embs
                    , freeSyms   = [(symbol v, v) | (_, v) <- syms] }

makeGhcSpec4 :: [Qualifier]
             -> [Var]
             -> [(ModName,Ms.Spec ty bndr)]
             -> ModName
             -> Subst
             -> GhcSpec
             -> BareM GhcSpec
makeGhcSpec4 quals defVars specs name su sp
  = do decr'   <- mconcat <$> mapM (makeHints defVars . snd) specs
       texprs' <- mconcat <$> mapM (makeTExpr defVars . snd) specs
       lazies  <- mkThing makeLazy
       lvars'  <- mkThing makeLVar
       asize'  <- S.fromList <$> makeASize
       hmeas   <- mkThing makeHMeas
       hinls   <- mkThing makeHInlines
       mapM_ (\(v, s) -> insertAxiom (val v) (val s)) $ S.toList hmeas
       mapM_ (\(v, s) -> insertAxiom (val v) (val s)) $ S.toList hinls
       mapM_ insertHMeasLogicEnv $ S.toList hmeas
       mapM_ insertHMeasLogicEnv $ S.toList hinls
       lmap'   <- logicEnv <$> get
       let isgs = strengthenHaskellInlines  (S.map fst hinls) (tySigs sp)
       let msgs = strengthenHaskellMeasures (S.map fst hmeas) isgs
       lmap    <- logicEnv <$> get
       inlmap  <- inlines  <$> get
       let f    = fmap $ txRefToLogic lmap inlmap
       let tx   = mapSnd f
       let mtx  = txRefToLogic lmap inlmap
       let txdcons d = d{tyRes = f $ tyRes d, tyConsts = f <$> tyConsts d, tyArgs = tx <$> tyArgs d}
       return   $ sp { qualifiers = subst su quals
                     , decr       = decr'
                     , lvars      = lvars'
                     , autosize   = asize'
                     , lazy       = S.insert dictionaryVar lazies
                     , tySigs     = tx  <$> msgs
                     , asmSigs    = tx  <$> asmSigs  sp
                     , inSigs     = tx  <$> inSigs   sp
                     , measures   = mtx <$> measures sp
                     , logicMap   = lmap'
                     , invariants = tx <$> invariants sp
                     , ctors      = tx <$> ctors      sp
                     , ialiases   = tx <$> ialiases   sp
                     , dconsP     = mapSnd txdcons <$> dconsP sp
                     , texprs     = mapSnd f <$> texprs'
                     }
    where
       mkThing mk = S.fromList . mconcat <$> sequence [ mk defVars s | (m, s) <- specs, m == name ]
       makeASize  = mapM lookupGhcTyCon [v | (m, s) <- specs, m == name, v <- S.toList (Ms.autosize s)]


insertHMeasLogicEnv :: (Located Var, LocSymbol) -> BareM ()
insertHMeasLogicEnv (x, s)
  | isBool res
  = insertLogicEnv (val s) (fst <$> vxs) $ mkProp $ mkEApp s ((EVar . fst) <$> vxs)
  where
    rep = toRTypeRep  t
    res = ty_res rep
    xs  = intSymbol (symbol ("x" :: String)) <$> [1..length $ ty_binds rep]
    vxs = dropWhile (isClassType.snd) $ zip xs (ty_args rep)
    t   = (ofType $ varType $ val x) :: SpecType
insertHMeasLogicEnv _
  = return ()

makeGhcSpecCHOP1
  :: Maybe [ClsInst] -> Config -> [(ModName,Ms.Spec ty bndr)]
  -> BareM ([(TyCon,TyConP)],[(DataCon,DataConP)],[Measure SpecType DataCon],[(Var,Located SpecType)],M.HashMap TyCon RTyCon,TCEmb TyCon)
makeGhcSpecCHOP1 instenv cfg specs
  = do (tcs, dcs)      <- mconcat <$> mapM makeConTypes specs
       let tycons       = tcs        ++ wiredTyCons
       let tyi          = makeTyConInfo tycons
       embs            <- makeNumericInfo instenv <$> (mconcat <$> mapM makeTyConEmbeds specs)
       datacons        <- makePluggedDataCons embs tyi (concat dcs ++ wiredDataCons)
       let dcSelectors  = concatMap (makeMeasureSelectors (exactDC cfg)) datacons
       recSels         <- makeRecordSelectorSigs datacons
       return             (tycons, second val <$> datacons, dcSelectors, recSels, tyi, embs)

makeGhcSpecCHOP3 :: Config -> [Var] -> [Var] -> [(ModName, Ms.BareSpec)]
                 -> ModName -> [(ModName, Var, LocSpecType)]
                 -> TCEmb TyCon
                 -> BareM ( [(Maybe Var, LocSpecType)]
                          , [(LocSpecType, LocSpecType)]
                          , [(Var, LocSpecType)]
                          , [(Var, LocSpecType)] )
makeGhcSpecCHOP3 cfg vars defVars specs name mts embs
  = do sigs'    <- mconcat <$> mapM (makeAssertSpec name cfg vars defVars) specs
       asms'    <- mconcat <$> mapM (makeAssumeSpec name cfg vars defVars) specs
       invs     <- mconcat <$> mapM makeInvariants specs
       ialias   <- mconcat <$> mapM makeIAliases   specs
       let dms   = makeDefaultMethods vars mts
       tyi      <- gets tcEnv
       let sigs  = [ (x, txRefSort tyi embs $ fmap txExpToBind t) | (_, x, t) <- sigs' ++ mts ++ dms ]
       let asms  = [ (x, txRefSort tyi embs $ fmap txExpToBind t) | (_, x, t) <- asms' ]
       let hms   = concatMap (S.toList . Ms.hmeas . snd) (filter ((==name) . fst) specs)
       let minvs = makeMeasureInvariants sigs hms
       return     (invs ++ minvs, ialias, sigs, asms)


symbol' :: Var -> Symbol
symbol' = dropModuleNames . symbol . getName

makeMeasureInvariants :: [(Var, LocSpecType)] -> [LocSymbol] -> [(Maybe Var, LocSpecType)]
makeMeasureInvariants sigs xs = measureTypeToInv <$> [(x, (y, ty)) | x <- xs, (y, ty) <- sigs, val x == symbol' y]

measureTypeToInv :: (LocSymbol, (Var, LocSpecType)) -> (Maybe Var, LocSpecType)
measureTypeToInv (x, (v, t)) = (Just v, t {val = mtype})
  where
    trep = toRTypeRep $ val t
    ts   = ty_args trep
    mtype
      | isBool $ ty_res trep
      = uError $ ErrHMeas (sourcePosSrcSpan $ loc t) (pprint x)
                          (text "Specification of boolean measures is not allowed")
{-
      | [tx] <- ts, not (isTauto tx)
      = uError $ ErrHMeas (sourcePosSrcSpan $ loc t) (pprint x)
                          (text "Measures' types cannot have preconditions")
-}
      | [tx] <- ts
      = mkInvariant (head $ ty_binds trep) tx $ ty_res trep
      | otherwise
      = uError $ ErrHMeas (sourcePosSrcSpan $ loc t) (pprint x)
                          (text "Measures has more than one arguments")


    mkInvariant :: Symbol -> SpecType -> SpecType -> SpecType
    mkInvariant z t tr = strengthen (top <$> t) (MkUReft reft mempty mempty)
      where
        Reft (v, p) = toReft $ fromMaybe mempty $ stripRTypeBase tr
        su    = mkSubst [(v, mkEApp x [EVar v])]
        reft  = Reft (v, subst su p')

        p'    = pAnd $ filter (\e -> z `notElem` syms e) $ conjuncts p

makeGhcSpecCHOP2 :: [CoreBind]
                 -> [(ModName, Ms.BareSpec)]
                 -> [Measure SpecType DataCon]
                 -> [(DataCon, DataConP)]
                 -> [(DataCon, DataConP)]
                 -> TCEmb TyCon
                 -> BareM ( MSpec SpecType DataCon
                          , [(Symbol, Located (RRType Reft))]
                          , [(Symbol, Located (RRType Reft))]
                          , [(Var,    LocSpecType)]
                          , [Symbol] )
makeGhcSpecCHOP2 cbs specs dcSelectors datacons cls embs
  = do measures'   <- mconcat <$> mapM makeMeasureSpec specs
       tyi         <- gets tcEnv
       name        <- gets modName
       mapM_ (makeHaskellInlines embs cbs name) specs
       hmeans      <- mapM (makeHaskellMeasures embs cbs name) specs
       let measures = mconcat (Ms.wiredInMeasures:measures':Ms.mkMSpec' dcSelectors:hmeans)
       let (cs, ms) = makeMeasureSpec' measures
       let cms      = makeClassMeasureSpec measures
       let cms'     = [ (x, Loc l l' $ cSort t) | (Loc l l' x, t) <- cms ]
       let ms'      = [ (x, Loc l l' t) | (Loc l l' x, t) <- ms, isNothing $ lookup x cms' ]
       let cs'      = [ (v, txRefSort' v tyi embs t) | (v, t) <- meetDataConSpec cs (datacons ++ cls)]
       let xs'      = val . fst <$> ms
       return (measures, cms', ms', cs', xs')

txRefSort'
  :: NamedThing a
  => a -> TCEnv -> TCEmb TyCon -> SpecType -> Located SpecType
txRefSort' v tyi embs t = txRefSort tyi embs (atLoc' v t)

atLoc' :: NamedThing a1 => a1 -> a -> Located a
atLoc' v = Loc (getSourcePos v) (getSourcePosE v)

data ReplaceEnv = RE { _re_env  :: M.HashMap Symbol Symbol
                     , _re_fenv :: SEnv SortedReft
                     , _re_emb  :: TCEmb TyCon
                     , _re_tyi  :: M.HashMap TyCon RTyCon
                     }

type ReplaceState = ( M.HashMap Var LocSpecType
                    , M.HashMap Var [Located Expr]
                    )

type ReplaceM = ReaderT ReplaceEnv (State ReplaceState)

replaceLocalBinds :: Bool
                  -> TCEmb TyCon
                  -> M.HashMap TyCon RTyCon
                  -> [(Var, LocSpecType)]
                  -> [(Var, [Located Expr])]
                  -> SEnv SortedReft
                  -> CoreProgram
                  -> ([(Var, LocSpecType)], [(Var, [Located Expr])])
replaceLocalBinds allowHO emb tyi sigs texprs senv cbs
  = (M.toList s, M.toList t)
  where
    (s, t) = execState (runReaderT (mapM_ (\x -> traverseBinds allowHO x (return ())) cbs)
                                   (RE M.empty senv emb tyi))
                       (M.fromList sigs, M.fromList texprs)

traverseExprs
  :: Bool -> CoreSyn.Expr Var -> ReaderT ReplaceEnv (State ReplaceState) ()
traverseExprs allowHO (Let b e)
  = traverseBinds allowHO b (traverseExprs allowHO e)
traverseExprs allowHO (Lam b e)
  = withExtendedEnv allowHO [b] (traverseExprs allowHO e)
traverseExprs allowHO (App x y)
  = traverseExprs allowHO x >> traverseExprs allowHO y
traverseExprs allowHO (Case e _ _ as)
  = traverseExprs allowHO e >> mapM_ (traverseExprs allowHO . thd3) as
traverseExprs allowHO (Cast e _)
  = traverseExprs allowHO e
traverseExprs allowHO (Tick _ e)
  = traverseExprs allowHO e
traverseExprs _ _
  = return ()

traverseBinds
  :: Bool
  -> Bind Var
  -> ReaderT ReplaceEnv (State ReplaceState) b
  -> ReaderT ReplaceEnv (State ReplaceState) b
traverseBinds allowHO b k = withExtendedEnv allowHO (bindersOf b) $ do
  mapM_ (traverseExprs allowHO) (rhssOfBind b)
  k

-- RJ: this function is incomprehensible, what does it do?!
withExtendedEnv
  :: Foldable t
  => Bool
  -> t Var
  -> ReaderT ReplaceEnv (State ReplaceState) b
  -> ReaderT ReplaceEnv (State ReplaceState) b
withExtendedEnv allowHO vs k
  = do RE env' fenv' emb tyi <- ask
       let env  = L.foldl' (\m v -> M.insert (varShortSymbol v) (symbol v) m) env' vs
           fenv = L.foldl' (\m v -> insertSEnv (symbol v) (rTypeSortedReft emb (ofType $ varType v :: RSort)) m) fenv' vs
       withReaderT (const (RE env fenv emb tyi)) $ do
         mapM_ (replaceLocalBindsOne allowHO) vs
         k

varShortSymbol :: Var -> Symbol
varShortSymbol = symbol . takeWhile (/= '#') . showPpr . getName

-- RJ: this function is incomprehensible
replaceLocalBindsOne :: Bool -> Var -> ReplaceM ()
replaceLocalBindsOne allowHO v
  = do mt <- gets (M.lookup v . fst)
       case mt of
         Nothing -> return ()
         Just (Loc l l' (toRTypeRep -> t@(RTypeRep {..}))) -> do
           (RE env' fenv emb tyi) <- ask
           let f m k = M.lookupDefault k k m
           let (env,args) = L.mapAccumL (\e (v, t) -> (M.insert v v e, substa (f e) t))
                             env' (zip ty_binds ty_args)
           let res  = substa (f env) ty_res
           let t'   = fromRTypeRep $ t { ty_args = args, ty_res = res }
           let msg  = ErrTySpec (sourcePosSrcSpan l) (pprint v) t'
           case checkTy allowHO msg emb tyi fenv (Loc l l' t') of
             Just err -> Ex.throw err
             Nothing -> modify (first $ M.insert v (Loc l l' t'))
           mes <- gets (M.lookup v . snd)
           case mes of
             Nothing -> return ()
             Just es -> do
               let es'  = substa (f env) es
               case checkTerminationExpr emb fenv (v, Loc l l' t', es') of
                 Just err -> Ex.throw err
                 Nothing  -> modify (second $ M.insert v es')
