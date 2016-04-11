{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ViewPatterns              #-}

module Language.Haskell.Liquid.Bare.GhcSpec (
    GhcSpec(..)
  , makeGhcSpec
  ) where

-- import Debug.Trace (trace)
import Prelude hiding (error)
import CoreSyn hiding (Expr)
import HscTypes
import Id
import NameSet
import Name
import TyCon
import Var
import TysWiredIn

import DataCon (DataCon)

import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor
import Data.Maybe


import Control.Monad.Except (catchError)
import TypeRep (Type(TyConApp))

import qualified Control.Exception   as Ex
import qualified Data.List           as L
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S

import Language.Fixpoint.Misc (thd3)

import Language.Fixpoint.Types hiding (Error)

import Language.Haskell.Liquid.Types.Dictionaries
import Language.Haskell.Liquid.GHC.Misc (showPpr, getSourcePosE, getSourcePos, sourcePosSrcSpan, isDataConId)
import Language.Haskell.Liquid.Types.PredType (makeTyConInfo)
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Misc (mapSnd)
import Language.Haskell.Liquid.WiredIn



import qualified Language.Haskell.Liquid.Measure as Ms

import Language.Haskell.Liquid.Bare.Check
import Language.Haskell.Liquid.Bare.DataType
import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Existential
import Language.Haskell.Liquid.Bare.Measure
import Language.Haskell.Liquid.Bare.Axiom
import Language.Haskell.Liquid.Bare.Misc (makeSymbols, mkVarExpr)
import Language.Haskell.Liquid.Bare.Plugged
import Language.Haskell.Liquid.Bare.RTEnv
import Language.Haskell.Liquid.Bare.Spec
import Language.Haskell.Liquid.Bare.SymSort
import Language.Haskell.Liquid.Bare.RefToLogic
import Language.Haskell.Liquid.Bare.Lookup (lookupGhcTyCon)

--------------------------------------------------------------------------------
makeGhcSpec :: Config
            -> ModName
            -> [CoreBind]
            -> [Var]
            -> [Var]
            -> NameSet
            -> HscEnv
            -> Either Error LogicMap
            -> [(ModName,Ms.BareSpec)]
            -> IO GhcSpec
--------------------------------------------------------------------------------
makeGhcSpec cfg name cbs vars defVars exports env lmap specs

  = do sp <- throwLeft =<< execBare act initEnv
       let renv = ghcSpecEnv sp
       throwLeft . checkGhcSpec specs renv $ postProcess cbs renv sp
  where
    act       = makeGhcSpec' cfg cbs vars defVars exports specs
    throwLeft = either Ex.throw return
    initEnv   = BE name mempty mempty mempty env lmap' mempty mempty
    lmap'     = case lmap of {Left e -> Ex.throw e; Right x -> x `mappend` listLMap}

listLMap = toLogicMap [(nilName, [], hNil),
                       (consName, [x, xs], hCons (EVar <$> [x,xs]))
                      ]
  where
    x  = symbol "x"
    xs = symbol "xs"
    hNil    = mkEApp (dummyLoc $ symbol nilDataCon ) []
    hCons   = mkEApp (dummyLoc $ symbol consDataCon)

postProcess :: [CoreBind] -> SEnv SortedReft -> GhcSpec -> GhcSpec
postProcess cbs specEnv sp@(SP {..})
  = sp { tySigs = tySigs', texprs = ts, asmSigs = asmSigs', dicts = dicts', invariants = invs', meas = meas', inSigs = inSigs' }
  where
    (sigs, ts')   = replaceLocalBinds tcEmbeds tyconEnv tySigs texprs specEnv cbs
    (assms, ts'') = replaceLocalBinds tcEmbeds tyconEnv asmSigs ts'   specEnv cbs
    (insigs, ts)  = replaceLocalBinds tcEmbeds tyconEnv inSigs  ts''  specEnv cbs
    tySigs'     = mapSnd (addTyConInfo tcEmbeds tyconEnv <$>) <$> sigs
    asmSigs'    = mapSnd (addTyConInfo tcEmbeds tyconEnv <$>) <$> assms
    inSigs'     = mapSnd (addTyConInfo tcEmbeds tyconEnv <$>) <$> insigs
    dicts'      = dmapty (addTyConInfo tcEmbeds tyconEnv) dicts
    invs'       = (addTyConInfo tcEmbeds tyconEnv <$>) <$> invariants
    meas'       = mapSnd (fmap (addTyConInfo tcEmbeds tyconEnv) . txRefSort tyconEnv tcEmbeds) <$> meas

ghcSpecEnv :: GhcSpec -> SEnv SortedReft
ghcSpecEnv sp        = fromListSEnv binds
  where
    emb              = tcEmbeds sp
    binds            =  [(x,        rSort t) | (x, Loc _ _ t) <- meas sp]
                     ++ [(symbol v, rSort t) | (v, Loc _ _ t) <- ctors sp]
                     ++ [(x,        vSort v) | (x, v) <- freeSyms sp, isConLikeId v]
                     -- ++ [(val x   , rSort stringrSort) | Just (ELit x s) <- mkLit <$> lconsts, isString s]
    rSort            = rTypeSortedReft emb
    vSort            = rSort . varRSort
    varRSort         :: Var -> RSort
    varRSort         = ofType . varType
    --lconsts          = literals cbs
    --stringrSort      :: RSort
    --stringrSort      = ofType stringTy
    --isString s       = rTypeSort emb stringrSort == s

------------------------------------------------------------------------------------------------
makeGhcSpec' :: Config -> [CoreBind] -> [Var] -> [Var] -> NameSet -> [(ModName, Ms.BareSpec)] -> BareM GhcSpec
------------------------------------------------------------------------------------------------
makeGhcSpec' cfg cbs vars defVars exports specs
  = do name          <- modName <$> get
       makeRTEnv  specs
       (tycons, datacons, dcSs, recSs, tyi, embs) <- makeGhcSpecCHOP1 specs
       makeBounds embs name defVars cbs specs
       modify                                   $ \be -> be { tcEnv = tyi }
       (cls, mts)                              <- second mconcat . unzip . mconcat <$> mapM (makeClasses name cfg vars) specs
       (measures, cms', ms', cs', xs')         <- makeGhcSpecCHOP2 cbs specs dcSs datacons cls embs
       (invs, ialias, sigs, asms)              <- makeGhcSpecCHOP3 cfg vars defVars specs name mts embs
       quals   <- mconcat <$> mapM makeQualifiers specs
       syms                                    <- makeSymbols (varInModule name) (vars ++ map fst cs') xs' (sigs ++ asms ++ cs') ms' (invs ++ (snd <$> ialias)) quals
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
addProofType spec
  = do tycon <- (Just <$> (lookupGhcTyCon $ dummyLoc proofTyConName)) `catchError` (\_ -> return Nothing)
       return $ spec {proofType = (`TyConApp` []) <$> tycon}


makeExactDataCons :: ModName -> Bool -> [Var] -> GhcSpec -> BareM GhcSpec
makeExactDataCons n flag vs spec
  | flag      = return $ spec {tySigs = (tySigs spec) ++ xts}
  | otherwise = return spec
  where
    xts = makeExact <$> (filter isDataConId $ filter (varInModule n) vs)

varInModule n v = L.isPrefixOf (show n) $ show v

makeExact :: Var -> (Var, Located SpecType)
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


makeGhcSpec0 cfg defVars exports name sp
  = do targetVars <- makeTargetVars name defVars $ binders cfg
       return      $ sp { config = cfg
                        , exports = exports
                        , tgtVars = targetVars }

makeGhcSpec1 vars defVars embs tyi exports name sigs asms cs' ms' cms' su sp
  = do tySigs      <- makePluggedSigs name embs tyi exports $ tx sigs
       asmSigs     <- makePluggedAsmSigs embs tyi $ tx asms
       ctors       <- makePluggedAsmSigs embs tyi $ tx cs'
       lmap        <- logicEnv <$> get
       inlmap      <- inlines  <$> get
       let ctors'   = [ (x, txRefToLogic lmap inlmap <$> t) | (x, t) <- ctors ]
       return $ sp { tySigs     = filter (\(v,_) -> v `elem` vs) tySigs
                   , asmSigs    = filter (\(v,_) -> v `elem` vs) asmSigs
                   , ctors      = filter (\(v,_) -> v `elem` vs) ctors'
                   , meas       = tx' $ tx $ ms' ++ varMeasures vars ++ cms' }
    where
      tx   = fmap . mapSnd . subst $ su
      tx'  = fmap (mapSnd $ fmap uRType)
      vs   = vars ++ defVars

makeGhcSpec2 invs ialias measures su sp
  = return $ sp { invariants = subst su invs
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

makeGhcSpec4 quals defVars specs name su sp
  = do decr'   <- mconcat <$> mapM (makeHints defVars . snd) specs
       texprs' <- mconcat <$> mapM (makeTExpr defVars . snd) specs
       lazies  <- mkThing makeLazy
       lvars'  <- mkThing makeLVar
       asize'  <- S.fromList <$> makeASize
       hmeas   <- mkThing makeHIMeas
       let msgs = strengthenHaskellMeasures hmeas
       lmap    <- logicEnv <$> get
       inlmap  <- inlines  <$> get
       let tx   = mapSnd (fmap $ txRefToLogic lmap inlmap)
       let mtx  = txRefToLogic lmap inlmap
       return   $ sp { qualifiers = subst su quals
                     , decr       = decr'
                     , texprs     = texprs'
                     , lvars      = lvars'
                     , autosize   = asize'
                     , lazy       = lazies
                     , tySigs     = tx  <$> tySigs  sp 
                     , asmSigs    = tx  <$> asmSigs sp
                     , measures   = mtx <$> measures sp
                     , inSigs     = tx  <$> msgs 
                     }
    where
       mkThing mk = S.fromList . mconcat <$> sequence [ mk defVars s | (m, s) <- specs, m == name ]
       makeASize  = mapM lookupGhcTyCon [v | (m, s) <- specs, m == name, v <- S.toList (Ms.autosize s)]

makeGhcSpecCHOP1 specs
  = do (tcs, dcs)      <- mconcat <$> mapM makeConTypes specs
       let tycons       = tcs        ++ wiredTyCons
       let tyi          = makeTyConInfo tycons
       embs            <- mconcat <$> mapM makeTyConEmbeds specs
       datacons        <- makePluggedDataCons embs tyi (concat dcs ++ wiredDataCons)
       let dcSelectors  = concatMap makeMeasureSelectors datacons
       recSels         <- makeRecordSelectorSigs datacons
       return             (tycons, second val <$> datacons, dcSelectors, recSels, tyi, embs)

makeGhcSpecCHOP3 cfg vars defVars specs name mts embs
  = do sigs'   <- mconcat <$> mapM (makeAssertSpec name cfg vars defVars) specs
       asms'   <- mconcat <$> mapM (makeAssumeSpec name cfg vars defVars) specs
       invs    <- mconcat <$> mapM makeInvariants specs
       ialias  <- mconcat <$> mapM makeIAliases   specs
       let dms  = makeDefaultMethods vars mts
       tyi     <- gets tcEnv
       let sigs = [ (x, txRefSort tyi embs $ fmap txExpToBind t) | (_, x, t) <- sigs' ++ mts ++ dms ]
       let asms = [ (x, txRefSort tyi embs $ fmap txExpToBind t) | (_, x, t) <- asms' ]
       return     (invs, ialias, sigs, asms)


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

txRefSort' v tyi embs t = txRefSort tyi embs (atLoc' v t)

atLoc' v = Loc (getSourcePos v) (getSourcePosE v)

data ReplaceEnv = RE { _re_env  :: M.HashMap Symbol Symbol
                     , _re_fenv :: SEnv SortedReft
                     , _re_emb  :: TCEmb TyCon
                     , _re_tyi  :: M.HashMap TyCon RTyCon
                     }

type ReplaceState = ( M.HashMap Var (Located SpecType)
                    , M.HashMap Var [Expr]
                    )

type ReplaceM = ReaderT ReplaceEnv (State ReplaceState)

replaceLocalBinds :: TCEmb TyCon
                  -> M.HashMap TyCon RTyCon
                  -> [(Var, Located SpecType)]
                  -> [(Var, [Expr])]
                  -> SEnv SortedReft
                  -> CoreProgram
                  -> ([(Var, Located SpecType)], [(Var, [Expr])])
replaceLocalBinds emb tyi sigs texprs senv cbs
  = (M.toList s, M.toList t)
  where
    (s,t) = execState (runReaderT (mapM_ (`traverseBinds` return ()) cbs)
                                  (RE M.empty senv emb tyi))
                      (M.fromList sigs, M.fromList texprs)

traverseExprs (Let b e)
  = traverseBinds b (traverseExprs e)
traverseExprs (Lam b e)
  = withExtendedEnv [b] (traverseExprs e)
traverseExprs (App x y)
  = traverseExprs x >> traverseExprs y
traverseExprs (Case e _ _ as)
  = traverseExprs e >> mapM_ (traverseExprs . thd3) as
traverseExprs (Cast e _)
  = traverseExprs e
traverseExprs (Tick _ e)
  = traverseExprs e
traverseExprs _
  = return ()

traverseBinds b k = withExtendedEnv (bindersOf b) $ do
  mapM_ traverseExprs (rhssOfBind b)
  k

-- RJ: this function is incomprehensible, what does it do?!
withExtendedEnv vs k
  = do RE env' fenv' emb tyi <- ask
       let env  = L.foldl' (\m v -> M.insert (varShortSymbol v) (symbol v) m) env' vs
           fenv = L.foldl' (\m v -> insertSEnv (symbol v) (rTypeSortedReft emb (ofType $ varType v :: RSort)) m) fenv' vs
       withReaderT (const (RE env fenv emb tyi)) $ do
         mapM_ replaceLocalBindsOne vs
         k

varShortSymbol :: Var -> Symbol
varShortSymbol = symbol . takeWhile (/= '#') . showPpr . getName

-- RJ: this function is incomprehensible
replaceLocalBindsOne :: Var -> ReplaceM ()
replaceLocalBindsOne v
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
           case checkTy msg emb tyi fenv (Loc l l' t') of
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
