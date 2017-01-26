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

import           Text.PrettyPrint.HughesPJ (text)

import qualified Control.Exception                          as Ex
import qualified Data.List                                  as L
import qualified Data.HashMap.Strict                        as M
import qualified Data.HashSet                               as S

import           Language.Fixpoint.Misc                     (thd3, mapSnd)
import           Language.Fixpoint.Types                    hiding (Error)

import           Language.Haskell.Liquid.Types.Dictionaries
import           Language.Haskell.Liquid.Misc               (concatMapM)
import           Language.Haskell.Liquid.GHC.Misc           (dropModuleUnique, dropModuleNames, showPpr, getSourcePosE, getSourcePos, sourcePosSrcSpan, isDataConId)
import           Language.Haskell.Liquid.Types.PredType     (makeTyConInfo)
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types
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
import           Language.Haskell.Liquid.Bare.Expand
import           Language.Haskell.Liquid.Bare.SymSort
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
            -> [(ModName, Ms.BareSpec)]
            -> IO GhcSpec
--------------------------------------------------------------------------------
makeGhcSpec cfg name cbs instenv vars defVars exports env lmap specs = do
  sp <- throwLeft =<< execBare act initEnv
  let renv = ghcSpecEnv sp
  throwLeft . checkGhcSpec specs renv $ postProcess cbs renv sp
  where
    act       = makeGhcSpec' cfg cbs instenv vars defVars exports specs
    throwLeft = either Ex.throw return
    initEnv   = BE name mempty mempty mempty env lmap' mempty mempty axs
    axs       = initAxSymbols name specs
    lmap'     = case lmap of { Left e -> Ex.throw e; Right x -> x `mappend` listLMap}

initAxSymbols :: ModName -> [(ModName, Ms.BareSpec)] -> M.HashMap Symbol LocSymbol
initAxSymbols name = locMap . Ms.axioms . fromMaybe mempty . lookup name
  where
    locMap xs      = M.fromList [ (val x, x) | x <- S.toList xs]

listLMap :: LogicMap
listLMap  = toLogicMap [ (dummyLoc nilName , []     , hNil)
                       , (dummyLoc consName, [x, xs], hCons (EVar <$> [x, xs])) ]
  where
    x     = symbol "x"
    xs    = symbol "xs"
    hNil  = mkEApp (dcSym nilDataCon ) []
    hCons = mkEApp (dcSym consDataCon)
    dcSym = dummyLoc . dropModuleUnique . symbol

postProcess :: [CoreBind] -> SEnv SortedReft -> GhcSpec -> GhcSpec
postProcess cbs specEnv sp@(SP {..})
  = sp { gsTySigs     = mapSnd addTCI <$> sigs
       , gsInSigs     = mapSnd addTCI <$> insigs
       , gsAsmSigs    = mapSnd addTCI <$> assms
       , gsInvariants = mapSnd addTCI <$> gsInvariants
       , gsLits       = txSort        <$> gsLits
       , gsMeas       = txSort        <$> gsMeas
       , gsDicts      = dmapty addTCI'    gsDicts
       , gsTexprs     = ts
       }
  where
    (sigs,   ts')     = replaceLocBinds gsTySigs  gsTexprs
    (assms,  ts'')    = replaceLocBinds gsAsmSigs ts'
    (insigs, ts)      = replaceLocBinds gsInSigs  ts''
    replaceLocBinds   = replaceLocalBinds allowHO gsTcEmbeds gsTyconEnv specEnv cbs
    txSort            = mapSnd (addTCI . txRefSort gsTyconEnv gsTcEmbeds)
    addTCI            = (addTCI' <$>)
    addTCI'           = addTyConInfo gsTcEmbeds gsTyconEnv
    allowHO           = higherOrderFlag gsConfig

ghcSpecEnv :: GhcSpec -> SEnv SortedReft
ghcSpecEnv sp        = fromListSEnv binds
  where
    emb              = gsTcEmbeds sp
    binds            =  [(x,        rSort t) | (x, Loc _ _ t) <- gsMeas sp]
                     ++ [(symbol v, rSort t) | (v, Loc _ _ t) <- gsCtors sp]
                     ++ [(x,        vSort v) | (x, v) <- gsFreeSyms sp, isConLikeId v]
    rSort            = rTypeSortedReft emb
    vSort            = rSort . varRSort
    varRSort         :: Var -> RSort
    varRSort         = ofType . varType

------------------------------------------------------------------------------------------------
makeGhcSpec' :: Config -> [CoreBind] -> Maybe [ClsInst] -> [Var] -> [Var] -> NameSet -> [(ModName, Ms.BareSpec)] -> BareM GhcSpec
------------------------------------------------------------------------------------------------
makeGhcSpec' cfg cbs instenv vars defVars exports specs
  = do name          <- modName <$> get
       embs          <- makeNumericInfo instenv <$> (mconcat <$> mapM makeTyConEmbeds specs)
       xils          <- concatMapM (makeHaskellInlines embs cbs name) specs
       lmap          <- logic_map . logicEnv <$> get
       makeRTEnv name xils specs lmap
       (tycons, datacons, dcSs, recSs, tyi) <- makeGhcSpecCHOP1 cfg specs embs
       makeBounds embs name defVars cbs specs
       modify                                   $ \be -> be { tcEnv = tyi }
       (cls, mts)                              <- second mconcat . unzip . mconcat <$> mapM (makeClasses name cfg vars) specs
       (measures, cms', ms', cs', xs')         <- makeGhcSpecCHOP2 cbs specs dcSs datacons cls embs
       (invs, ntys, ialias, sigs, asms)        <- makeGhcSpecCHOP3 cfg vars defVars specs name mts embs
       quals   <- mconcat <$> mapM makeQualifiers specs
       syms                                    <- makeSymbols (varInModule name) (vars ++ map fst cs') xs' (sigs ++ asms ++ cs') ms' (map snd invs ++ (snd <$> ialias))
       let su  = mkSubst [ (x, mkVarExpr v) | (x, v) <- syms]
       makeGhcSpec0 cfg defVars exports name (emptySpec cfg)
         >>= makeGhcSpec1 vars defVars embs tyi exports name sigs (recSs ++ asms) cs' ms' cms' su
         >>= makeGhcSpec2 invs ntys ialias measures su
         >>= makeGhcSpec3 (datacons ++ cls) tycons embs syms
         >>= makeSpecDictionaries embs vars specs
         >>= makeGhcAxioms embs cbs name specs
         >>= makeExactDataCons name (exactDC cfg) (snd <$> syms)
         -- This step need the updated logic map, ie should happen AFTER makeGhcAxioms
         >>= makeGhcSpec4 quals defVars specs name su
         >>= addProofType
         >>= addRTEnv

addProofType :: GhcSpec -> BareM GhcSpec
addProofType spec = do
  tycon <- (Just <$> lookupGhcTyCon (dummyLoc proofTyConName)) `catchError` (\_ -> return Nothing)
  return $ spec { gsProofType = (`TyConApp` []) <$> tycon }

addRTEnv :: GhcSpec -> BareM GhcSpec
addRTEnv spec = do
  rt <- rtEnv <$> get
  return $ spec { gsRTAliases = rt }


makeExactDataCons :: ModName -> Bool -> [Var] -> GhcSpec -> BareM GhcSpec
makeExactDataCons n flag vs spec
  | flag      = return $ spec { gsTySigs = gsTySigs spec ++ xts}
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
makeAxioms tce cbs spec sp = do
  lmap             <- logicEnv <$> get
  (msA, tysA, asA, smtA) <- L.unzip4 <$> mapM (makeAxiom tce lmap cbs spec sp) (S.toList $ Ms.axioms   sp)
  (msR, tysR, asR, _   ) <- L.unzip4 <$> mapM (makeAxiom tce lmap cbs spec sp) (S.toList $ Ms.reflects sp)
  lmap'            <- logicEnv <$> get
  return $ spec { gsMeas     = msA ++ msR ++ gsMeas     spec
                , gsAsmSigs  = concat tysA ++ concat tysR ++ gsAsmSigs  spec
                , gsReflects = concat asA  ++ concat asR  ++ gsReflects spec
                , gsAxioms   = smtA ++ gsAxioms spec 
                , gsLogicMap = lmap' }

emptySpec     :: Config -> GhcSpec
emptySpec cfg = SP
  { gsTySigs     = mempty
  , gsAsmSigs    = mempty
  , gsInSigs     = mempty
  , gsCtors      = mempty
  , gsLits       = mempty
  , gsMeas       = mempty
  , gsInvariants = mempty
  , gsIaliases   = mempty
  , gsDconsP     = mempty
  , gsTconsP     = mempty
  , gsFreeSyms   = mempty
  , gsTcEmbeds   = mempty
  , gsQualifiers = mempty
  , gsTgtVars    = mempty
  , gsDecr       = mempty
  , gsTexprs     = mempty
  , gsNewTypes   = mempty
  , gsLvars      = mempty
  , gsLazy       = mempty
  , gsAutoInst   = mempty
  , gsAutosize   = mempty
  , gsConfig     = cfg
  , gsExports    = mempty
  , gsMeasures   = mempty
  , gsTyconEnv   = mempty
  , gsDicts      = mempty
  , gsAxioms     = mempty
  , gsReflects   = mempty 
  , gsLogicMap   = mempty
  , gsProofType  = Nothing
  , gsRTAliases  = mempty
  }






makeGhcSpec0 :: Config
             -> [Var]
             -> NameSet
             -> ModName
             -> GhcSpec
             -> BareM GhcSpec
makeGhcSpec0 cfg defVars exports name sp
  = do targetVars <- makeTargetVars name defVars $ checks cfg
       return      $ sp { gsConfig  = cfg
                        , gsExports = exports
                        , gsTgtVars = targetVars }

makeGhcSpec1 :: [Var]
             -> [Var]
             -> TCEmb TyCon
             -> M.HashMap TyCon RTyCon
             -> NameSet
             -> ModName
             -> [(Var,    LocSpecType)]
             -> [(Var,    LocSpecType)]
             -> [(Var,    LocSpecType)]
             -> [(Symbol, Located (RRType Reft))]
             -> [(Symbol, Located (RRType Reft))]
             -> Subst
             -> GhcSpec
             -> BareM GhcSpec
makeGhcSpec1 vars defVars embs tyi exports name sigs asms cs' ms' cms' su sp
  = do tySigs      <- makePluggedSigs name embs tyi exports $ tx sigs
       asmSigs     <- makePluggedAsmSigs embs tyi $ tx asms
       ctors       <- makePluggedAsmSigs embs tyi $ tx cs'
       return $ sp { gsTySigs   = filter (\(v,_) -> v `elem` vs) tySigs
                   , gsAsmSigs  = filter (\(v,_) -> v `elem` vs) asmSigs
                   , gsCtors    = filter (\(v,_) -> v `elem` vs) ctors
                   , gsMeas     = measSyms
                   , gsLits     = measSyms -- RJ: we will be adding *more* things to `meas` but not `lits`
                   }
    where
      tx       = fmap . mapSnd . subst $ su
      tx'      = fmap (mapSnd $ fmap uRType)
      vs       = vars ++ defVars
      measSyms = tx' $ tx $ ms' ++ varMeasures vars ++ cms'

makeGhcSpec2 :: Monad m
             => [(Maybe Var  , LocSpecType)]
             -> [(TyCon      , LocSpecType)]
             -> [(LocSpecType, LocSpecType)]
             -> MSpec SpecType DataCon
             -> Subst
             -> GhcSpec
             -> m GhcSpec
makeGhcSpec2 invs ntys ialias measures su sp
  = return $ sp { gsInvariants = mapSnd (subst su) <$> invs
                , gsNewTypes   = mapSnd (subst su) <$> ntys
                , gsIaliases   = subst su ialias
                , gsMeasures   = subst su
                                 <$> M.elems (Ms.measMap measures)
                                  ++ Ms.imeas measures
                }

makeGhcSpec3 :: [(DataCon, DataConP)] -> [(TyCon, TyConP)] -> TCEmb TyCon -> [(t, Var)] -> GhcSpec -> BareM GhcSpec
makeGhcSpec3 datacons tycons embs syms sp = do
  tcEnv  <- tcEnv    <$> get
  return  $ sp { gsTyconEnv = tcEnv
               , gsDconsP   = datacons -- dcons'
               , gsTconsP   = tycons
               , gsTcEmbeds = embs
               , gsFreeSyms = [(symbol v, v) | (_, v) <- syms]
               }

makeGhcSpec4 :: [Qualifier]
             -> [Var]
             -> [(ModName, Ms.Spec ty bndr)]
             -> ModName
             -> Subst
             -> GhcSpec
             -> BareM GhcSpec
makeGhcSpec4 quals defVars specs name su sp
  = do decr'   <- mconcat <$> mapM (makeHints defVars . snd) specs
       gsTexprs' <- mconcat <$> mapM (makeTExpr defVars . snd) specs
       lazies  <- mkThing makeLazy
       autois  <- mkThing makeAutoInsts
       lvars'  <- mkThing makeLVar
       defs'   <- mkThing makeDefs
       mrefs   <- mkThing makeMReflects 
       addDefs defs'
       asize'  <- S.fromList <$> makeASize
       hmeas   <- mkThing makeHMeas
       hinls   <- mkThing makeHInlines
       mapM_ (\(v, s) -> insertAxiom v s) mrefs 
       mapM_ (\(v, s) -> insertAxiom (val v) (val s)) $ S.toList hmeas
       mapM_ (\(v, s) -> insertAxiom (val v) (val s)) $ S.toList hinls
       mapM_ insertHMeasLogicEnv $ S.toList hmeas
       mapM_ insertHMeasLogicEnv $ S.toList hinls
       lmap'       <- logicEnv <$> get
       isgs        <- expand $ strengthenHaskellInlines  (S.map fst hinls) (gsTySigs sp)
       gsTySigs'   <- expand $ strengthenHaskellMeasures (S.map fst hmeas) isgs
       gsMeasures' <- expand $ gsMeasures   sp
       gsAsmSigs'  <- expand $ gsAsmSigs    sp
       gsInSigs'   <- expand $ gsInSigs     sp
       gsInvarnts' <- expand $ gsInvariants sp
       gsCtors'    <- expand $ gsCtors      sp
       gsIaliases' <- expand $ gsIaliases   sp
       gsDconsP'   <- expand $ gsDconsP     sp
       return   $ sp { gsQualifiers = subst su quals
                     , gsDecr       = decr'
                     , gsLvars      = lvars'
                     , gsAutoInst   = M.fromList $ S.toList autois
                     , gsAutosize   = asize'
                     , gsLazy       = S.insert dictionaryVar lazies
                     , gsLogicMap   = lmap'
                     , gsTySigs     = gsTySigs'
                     , gsTexprs     = gsTexprs'
                     , gsMeasures   = gsMeasures'
                     , gsAsmSigs    = gsAsmSigs'
                     , gsInSigs     = gsInSigs'
                     , gsInvariants = gsInvarnts'
                     , gsCtors      = gsCtors'
                     , gsIaliases   = gsIaliases'
                     , gsDconsP     = gsDconsP'
                     }
    where
       mkThing mk = S.fromList . mconcat <$> sequence [ mk defVars s | (m, s) <- specs, m == name ]
       makeASize  = mapM lookupGhcTyCon [v | (m, s) <- specs, m == name, v <- S.toList (Ms.autosize s)]

insertHMeasLogicEnv :: (Located Var, LocSymbol) -> BareM ()
insertHMeasLogicEnv (x, s)
  | isBool res
  = insertLogicEnv "insertHMeasLogicENV" s (fst <$> vxs) $ mkProp $ mkEApp s ((EVar . fst) <$> vxs)
  where
    rep = toRTypeRep  t
    res = ty_res rep
    xs  = intSymbol (symbol ("x" :: String)) <$> [1..length $ ty_binds rep]
    vxs = dropWhile (isClassType.snd) $ zip xs (ty_args rep)
    t   = (ofType $ varType $ val x) :: SpecType
insertHMeasLogicEnv _
  = return ()

makeGhcSpecCHOP1
  :: Config -> [(ModName,Ms.Spec ty bndr)] -> TCEmb TyCon
  -> BareM ( [(TyCon,TyConP)]
           , [(DataCon,DataConP)]
           , [Measure SpecType DataCon]
           , [(Var, Located SpecType)]
           , M.HashMap TyCon RTyCon     )
makeGhcSpecCHOP1 cfg specs embs = do
  (tcs, dcs)      <- mconcat <$> mapM makeConTypes specs
  let tycons       = tcs        ++ wiredTyCons
  let tyi          = makeTyConInfo tycons
  datacons        <- makePluggedDataCons embs tyi (concat dcs ++ wiredDataCons)
  let dcSelectors  = concatMap (makeMeasureSelectors (exactDC cfg) (not $ noMeasureFields cfg)) datacons
  recSels         <- makeRecordSelectorSigs datacons
  return             (tycons, second val <$> datacons, dcSelectors, recSels, tyi)

makeGhcSpecCHOP3 :: Config -> [Var] -> [Var] -> [(ModName, Ms.BareSpec)]
                 -> ModName -> [(ModName, Var, LocSpecType)]
                 -> TCEmb TyCon
                 -> BareM ( [(Maybe Var, LocSpecType)]
                          , [(TyCon, LocSpecType)]
                          , [(LocSpecType, LocSpecType)]
                          , [(Var, LocSpecType)]
                          , [(Var, LocSpecType)] )
makeGhcSpecCHOP3 cfg vars defVars specs name mts embs
  = do sigs'    <- mconcat <$> mapM (makeAssertSpec name cfg vars defVars) specs
       asms'    <- mconcat <$> mapM (makeAssumeSpec name cfg vars defVars) specs
       invs     <- mconcat <$> mapM makeInvariants specs
       ialias   <- mconcat <$> mapM makeIAliases   specs
       ntys     <- mconcat <$> mapM makeNewTypes   specs
       let dms   = makeDefaultMethods vars mts
       tyi      <- gets tcEnv
       let sigs  = [ (x, txRefSort tyi embs $ fmap txExpToBind t) | (_, x, t) <- sigs' ++ mts ++ dms ]
       let asms  = [ (x, txRefSort tyi embs $ fmap txExpToBind t) | (_, x, t) <- asms' ]
       let hms   = concatMap (S.toList . Ms.hmeas . snd) (filter ((==name) . fst) specs)
       let minvs = makeMeasureInvariants sigs hms
       return     (invs ++ minvs, ntys, ialias, sigs, asms)


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
       hmeans      <- mapM (makeHaskellMeasures embs cbs name) specs
       let measures = mconcat (measures':Ms.mkMSpec' dcSelectors:hmeans)
       let (cs, ms) = makeMeasureSpec' measures
       let cms      = makeClassMeasureSpec measures
       let cms'     = [ (x, Loc l l' $ cSort t) | (Loc l l' x, t) <- cms ]
       let ms'      = [ (x, Loc l l' t) | (Loc l l' x, t) <- ms, isNothing $ lookup x cms' ]
       let cs'      = [ (v, txRefSort' v tyi embs t) | (v, t) <- meetDataConSpec cs (datacons ++ cls)]
       let xs'      = val . fst <$> ms
       return (measures, cms', ms', cs', xs')

txRefSort' :: NamedThing a => a -> TCEnv -> TCEmb TyCon -> SpecType -> LocSpecType
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

-- RJ: WHAT DOES THIS FUNCTION DO?!!!!
replaceLocalBinds :: Bool
                  -> TCEmb TyCon
                  -> M.HashMap TyCon RTyCon
                  -> SEnv SortedReft
                  -> CoreProgram
                  -> [(Var, LocSpecType)]
                  -> [(Var, [Located Expr])]
                  -> ([(Var, LocSpecType)], [(Var, [Located Expr])])
replaceLocalBinds allowHO emb tyi senv cbs sigs texprs
  = (M.toList s, M.toList t)
  where
    (s, t) = execState (runReaderT (mapM_ (\x -> traverseBinds allowHO x (return ())) cbs)
                                   (RE M.empty senv emb tyi))
                       (M.fromList sigs, M.fromList texprs)

traverseExprs :: Bool -> CoreSyn.Expr Var -> ReplaceM ()
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

traverseBinds :: Bool -> Bind Var -> ReplaceM b -> ReplaceM b
traverseBinds allowHO b k = withExtendedEnv allowHO (bindersOf b) $ do
  mapM_ (traverseExprs allowHO) (rhssOfBind b)
  k

-- RJ: this function is incomprehensible, what does it do?!
withExtendedEnv :: Bool -> [Var] -> ReplaceM b -> ReplaceM b
withExtendedEnv allowHO vs k = do
  RE env' fenv' emb tyi <- ask
  let env  = L.foldl' (\m v -> M.insert (varShortSymbol v) (symbol v) m) env' vs
      fenv = L.foldl' (\m v -> insertSEnv (symbol v) (rTypeSortedReft emb (ofType $ varType v :: RSort)) m) fenv' vs
  withReaderT (const (RE env fenv emb tyi)) $ do
    mapM_ (replaceLocalBindsOne allowHO) vs
    k

varShortSymbol :: Var -> Symbol
varShortSymbol = symbol . takeWhile (/= '#') . showPpr . getName

-- RJ: this function is incomprehensible, what does it do?!
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
             Nothing  -> modify (first $ M.insert v (Loc l l' t'))
           mes <- gets (M.lookup v . snd)
           case mes of
             Nothing -> return ()
             Just es -> do
               let es'  = substa (f env) es
               case checkTerminationExpr emb fenv (v, Loc l l' t', es') of
                 Just err -> Ex.throw err
                 Nothing  -> modify (second $ M.insert v es')
