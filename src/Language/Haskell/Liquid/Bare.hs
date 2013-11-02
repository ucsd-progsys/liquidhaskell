{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, ScopedTypeVariables, RecordWildCards, ParallelListComp  #-}

-- | This module contains the functions that convert /from/ descriptions of 
-- symbols, names and types (over freshly parsed /bare/ Strings),
-- /to/ representations connected to GHC vars, names, and types.
-- The actual /representations/ of bare and real (refinement) types are all
-- in `RefType` -- they are different instances of `RType`

module Language.Haskell.Liquid.Bare (
    GhcSpec (..)
  , makeGhcSpec
  -- , varSpecType
  ) where

import GHC hiding               (lookupName, Located)
import Text.PrettyPrint.HughesPJ    hiding (first)
import Var
import Name                     (getSrcSpan)
import Id                       (isConLikeId)
import PrelNames
import PrelInfo                 (wiredInThings)
import Type                     (expandTypeSynonyms, splitFunTy_maybe, eqType)
import DataCon                  (dataConImplicitIds, dataConWorkId, dataConStupidTheta)
import TyCon                    (tyConArity)
import HscMain
import TysWiredIn
import BasicTypes               (TupleSort (..), Arity)
import TcRnDriver               (tcRnLookupRdrName, tcRnLookupName)
import RdrName                  (setRdrNameSpace, mkRdrUnqual)
import OccName                  (tcName, mkDataOcc)
import Data.Char                (isLower, isUpper)
import Text.Printf
import Data.Maybe               (listToMaybe, fromMaybe, mapMaybe, catMaybes, isNothing, fromJust)
import Control.Monad.State      (put, get, gets, modify, State, evalState, evalStateT, execState, StateT)
import Data.Traversable         (forM)
import Control.Applicative      ((<$>), (<*>), (<|>), pure)
import Control.Monad.Reader     hiding (forM)
import Control.Monad.Error      hiding (Error, forM)
import Control.Monad.Writer     hiding (forM)
import qualified Control.Exception as Ex 
-- import Data.Data                hiding (TyCon, tyConName)
import Data.Bifunctor
import Data.Function            (on)

import Language.Fixpoint.Misc
import Language.Fixpoint.Names                  (propConName, takeModuleNames, dropModuleNames)
import Language.Fixpoint.Types                  hiding (Def, Predicate)
import Language.Fixpoint.Sort                   (checkSortedReftFull)
import Language.Haskell.Liquid.GhcMisc          hiding (L)
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.PredType hiding (unify)
import qualified Language.Haskell.Liquid.Measure as Ms

import qualified Data.List           as L
import qualified Data.HashSet        as S
import qualified Data.HashMap.Strict as M
import TypeRep
------------------------------------------------------------------
---------- Top Level Output --------------------------------------
------------------------------------------------------------------

makeGhcSpec :: Config -> ModName -> [Var] -> [Var] -> HscEnv
            -> [(ModName,Ms.Spec BareType Symbol)]
            -> IO GhcSpec
makeGhcSpec cfg name vars defVars env specs
  = either Ex.throw return . checkGhcSpec =<< execBare (makeGhcSpec' cfg vars defVars specs) initEnv
  where initEnv = BE name mempty mempty mempty env

checkMeasures emb env ms = concatMap (checkMeasure emb env) ms

checkMeasure :: M.HashMap TyCon FTycon-> SEnv SortedReft -> Measure SpecType DataCon -> [Error]
checkMeasure emb γ (M name@(Loc src n) sort body)
  = [txerror e | Just e <- checkMBody γ emb name sort <$> body]
  where 
    txerror = ErrMeas (sourcePosSrcSpan src) n

checkMBody γ emb name sort (Def s c bs body) = go γ' body
  where 
    γ'  = foldl (\γ (x, t) -> insertSEnv x t γ) γ xts
    xts = zip bs $ rTypeSortedReft emb . subsTyVars_meet su <$> ts
    ct  = ofType $ dataConUserType c :: SpecType
    su  = unify tr (head $ snd3 $ bkArrowDeep sort)

    (_, ts, tr) = bkArrow $ thd3 $ bkUniv ct 

    unify (RVar tv _) t                    = [(tv, toRSort t, t)]
    unify (RApp _ ts _ _) (RApp _ ts' _ _) = concat $ zipWith unify ts ts'
    unify _ _                              = []

    go γ (E e)   = checkSortedReftFull γ e
    go γ (P p)   = checkSortedReftFull γ p
    go γ (R s p) = checkSortedReftFull (insertSEnv s sty γ) p

    sty = rTypeSortedReft emb (thd3 $ bkArrowDeep sort)

makeGhcSpec' :: Config -> [Var] -> [Var]
             -> [(ModName,Ms.Spec BareType Symbol)]
             -> BareM (GhcSpec, [Measure SpecType DataCon])
makeGhcSpec' cfg vars defVars specs
  = do name <- gets modName
       makeRTEnv (concat [map (mod,) $ Ms.aliases  sp | (mod,sp) <- specs])
                 (concat [map (mod,) $ Ms.paliases sp | (mod,sp) <- specs])
       (tcs, dcs)      <- mconcat <$> mapM makeConTypes specs
       let (tcs', dcs') = wiredTyDataCons
       let tycons       = tcs ++ tcs'    
       let datacons     = concat dcs ++ dcs'
       modify $ \be -> be { tcEnv = makeTyConInfo tycons }
       measures        <- mconcat <$> mapM makeMeasureSpec specs
       let (cs, ms)     = makeMeasureSpec' measures
       let cms          = makeClassMeasureSpec measures
       sigs'           <- mconcat <$> mapM (makeAssumeSpec name cfg vars defVars) specs
       invs            <- mconcat <$> mapM makeInvariants specs
       embs            <- mconcat <$> mapM makeTyConEmbeds specs
       targetVars      <- makeTargetVars name defVars $ binders cfg
       lazies          <- mconcat <$> mapM makeLazies specs
       (cls,mts)       <- second mconcat . unzip . mconcat
                          <$> mapM (makeClasses cfg vars) specs
       tcEnv           <- gets tcEnv
       let sigs         = [ (x, (txRefSort tcEnv embs . txExpToBind) <$> t)
                          | (m, x, t) <- sigs'++mts ]
       let cs'          = mapSnd (Loc dummyPos) <$> meetDataConSpec cs (datacons++cls)
       let cms'         = [ (x, Loc l $ cSort t) | (Loc l x, t) <- cms ]
       let ms'          = [ (x, Loc l t) | (Loc l x, t) <- ms
                                         , isNothing $ lookup x cms' ]
       syms            <- makeSymbols (vars ++ map fst cs') (map fst ms) (sigs ++ cs') ms'
       let su           = mkSubst [ (x, mkVarExpr v) | (x, v) <- syms]
       let tx           = subsFreeSymbols su
       let txq          = subsFreeSymbolsQual su
       let syms'        = [(symbol v, v) | (_, v) <- syms]
       decr'           <- mconcat <$> mapM (makeHints defVars) specs
       lvars'          <- S.fromList . mconcat
                                    <$> sequence [ makeLVars defVars (mod,spec)
                                                 | (mod,spec) <- specs
                                                 , mod == name
                                                 ]
       quals           <- mconcat <$> mapM makeQualifiers specs
       return           $ (SP { tySigs     = renameTyVars <$> tx sigs
                              , ctors      = tx cs'
                              , meas       = tx (ms' ++ varMeasures vars ++ cms')
                              , invariants = invs
                              , dconsP     = datacons
                              , tconsP     = tycons 
                              , freeSyms   = syms'
                              , tcEmbeds   = embs 
                              , qualifiers = txq quals
                              , decr       = decr'
                              , lvars      = lvars'
                              , lazy       = lazies
                              , tgtVars    = targetVars
                              , config     = cfg
                              }
                          , subst su <$> M.elems $ Ms.measMap measures)

--- Refinement Type Aliases
makeRTEnv rts pts  = do initRTEnv
                        makeRPAliases pts
                        makeRTAliases rts
  where initRTEnv   = do forM_ rts $ \(mod,rta) -> setRTAlias (rtName rta) $ Left (mod,rta)
                         forM_ pts $ \(mod,pta) -> setRPAlias (rtName pta) $ Left (mod,pta)


makeRTAliases xts = mapM_ expBody xts
  where expBody (mod,xt) = inModule mod $ do
                             body <- withVArgs (rtVArgs xt) $ expandRTAlias $ rtBody xt
                             setRTAlias (rtName xt)
                               $ Right $ mapRTAVars stringRTyVar $ xt { rtBody = body }

makeRPAliases xts = mapM_ expBody xts
  where expBody (mod,xt) = inModule mod $ do
                             env  <- gets $ predAliases . rtEnv
                             body <- withVArgs (rtVArgs xt) $ expandRPAliasE $ rtBody xt
                             setRPAlias (rtName xt) $ Right $ xt { rtBody = body }

-- | Using the Alias Environment to Expand Definitions
expandRTAliasMeasure m
  = do eqns <- sequence $ expandRTAliasDef <$> (eqns m)
       return $ m { sort = generalize (sort m)
                  , eqns = eqns }

expandRTAliasDef :: Def Symbol -> BareM (Def Symbol)
expandRTAliasDef d
  = do env <- gets rtEnv
       body <- expandRTAliasBody env $ body d
       return $ d { body = body }

expandRTAliasBody :: RTEnv -> Body -> BareM Body
expandRTAliasBody env (P p)   = P   <$> (expPAlias p)
expandRTAliasBody env (R x p) = R x <$> (expPAlias p)
expandRTAliasBody _   (E e)   = E   <$> resolve e

expPAlias :: Pred -> BareM Pred
expPAlias = expandPAlias []


expandRTAlias   :: BareType -> BareM SpecType
expandRTAlias bt = expType =<< expReft bt
  where 
    expReft = mapReftM (txPredReft expPred)
    expType = expandAlias  []
    expPred = expandPAlias []

txPredReft :: (Pred -> BareM Pred) -> RReft -> BareM RReft
txPredReft f (U r p) = (`U` p) <$> txPredReft' f r
  where 
    txPredReft' f (Reft (v, ras)) = Reft . (v,) <$> mapM (txPredRefa f) ras
    txPredRefa  f (RConc p)       = RConc <$> f p
    txPredRefa  _ z               = return z

-- | Using the Alias Environment to Expand Definitions

expandRPAliasE = expandPAlias []

expandRTAliasE = expandAlias []

expandAlias s = go s
  where 
    go s (RApp c ts rs r)
      | c `elem` s        = errorstar $ "Cyclic Reftype Alias Definition: " ++ show (c:s)
      | otherwise = do
          env <- gets (typeAliases.rtEnv)
          case M.lookup c env of
            Just (Left (mod,rtb)) -> do
              st <- inModule mod $ withVArgs (rtVArgs rtb) $ expandAlias (c:s) $ rtBody rtb
              let rts = mapRTAVars stringRTyVar $ rtb { rtBody = st }
              setRTAlias c $ Right rts
              r' <- resolve r
              expandRTApp s rts ts r'
            Just (Right rts) -> do
              r' <- resolve r
              withVArgs (rtVArgs rts) $ expandRTApp s rts ts r'
            Nothing | isList c && length ts == 1 -> do
                      tyi <- tcEnv <$> get
                      r'  <- resolve r
                      liftM2 (bareTCApp tyi r' listTyCon) (mapM (go' s) rs) (mapM (go s) ts)
                    | isTuple c -> do
                      tyi <- tcEnv <$> get
                      r'  <- resolve r
                      let tc = tupleTyCon BoxedTuple (length ts)
                      liftM2 (bareTCApp tyi r' tc) (mapM (go' s) rs) (mapM (go s) ts)
                    | otherwise -> do
                      tyi <- tcEnv <$> get
                      r'  <- resolve r
                      liftM3 (bareTCApp tyi r') (lookupGhcTyCon c) (mapM (go' s) rs) (mapM (go s) ts)
    go s (RVar a r)       = RVar (stringRTyVar a) <$> resolve r
    go s (RFun x t t' r)  = rFun x <$> go s t <*> go s t'
    go s (RAppTy t t' r)  = RAppTy <$> go s t <*> go s t' <*> pure r
    go s (RAllE x t1 t2)  = liftM2 (RAllE x) (go s t1) (go s t2)
    go s (REx x t1 t2)    = liftM2 (REx x) (go s t1) (go s t2)
    go s (RAllT a t)      = RAllT (stringRTyVar a) <$> go s t
    go s (RAllP a t)      = RAllP <$> ofBPVar a <*> go s t
    go s (RCls c ts)      = RCls <$> lookupGhcClass c <*> (mapM (go s) ts)
    go _ (ROth s)         = return $ ROth s
    go _ (RExprArg e)     = return $ RExprArg e

    go' s (RMono ss r)    = RMono <$> mapM ofSyms ss <*> resolve r
    go' s (RPoly ss t)    = RPoly <$> mapM ofSyms ss <*> go s t

expandRTApp s rta args r
  | length args == (length αs) + (length εs)
  = do args'  <- mapM (expandAlias s) args
       let ts  = take (length αs) args'
           αts = zipWith (\α t -> (α, toRSort t, t)) αs ts
       return $ subst su . (`strengthen` r) . subsTyVars_meet αts $ rtBody rta
  | otherwise
  = errortext $ (text "Malformed Type-Alias Application" $+$ text msg)
  where
    su        = mkSubst $ zip (stringSymbol . showpp <$> εs) es
    αs        = rtTArgs rta 
    εs        = rtVArgs rta
    msg       = rtName rta ++ " " ++ join (map showpp args)
    es_       = drop (length αs) args
    es        = map (exprArg msg) es_
    
-- | exprArg converts a tyVar to an exprVar because parser cannot tell 
-- HORRIBLE HACK To allow treating upperCase X as value variables X
-- e.g. type Matrix a Row Col = List (List a Row) Col

exprArg _   (RExprArg e)     
  = e
exprArg _   (RVar x _)       
  = EVar (stringSymbol $ showpp x)
exprArg _   (RApp x [] [] _) 
  = EVar (stringSymbol $ showpp x)
exprArg msg (RApp f ts [] _) 
  = EApp (stringSymbol $ showpp f) (exprArg msg <$> ts)
exprArg msg (RAppTy (RVar f _) t _)   
  = EApp (stringSymbol $ showpp f) [exprArg msg t]
exprArg msg z 
  = errorstar $ printf "Unexpected expression parameter: %s in %s" (show z) msg 

expandPAlias :: [Symbol] -> Pred -> BareM Pred
expandPAlias s = go s
  where 
    go s p@(PBexp (EApp f es))  
      | f `elem` s                = errorstar $ "Cyclic Predicate Alias Definition: " ++ show (f:s)
      | otherwise = do
          env <- gets (predAliases.rtEnv)
          case M.lookup (symbolString f) env of
            Just (Left (mod,rp)) -> do
              body <- inModule mod $ withVArgs (rtVArgs rp) $ expandPAlias (f:s) $ rtBody rp
              let rp' = rp { rtBody = body }
              setRPAlias (show f) $ Right $ rp'
              expandRPApp (f:s) rp' <$> mapM resolve es
            Just (Right rp) ->
              withVArgs (rtVArgs rp) (expandRPApp (f:s) rp <$> mapM resolve es)
            Nothing -> fmap PBexp (EApp <$> resolve f <*> mapM resolve es)
    go s (PAnd ps)                = PAnd <$> (mapM (go s) ps)
    go s (POr  ps)                = POr  <$> (mapM (go s) ps)
    go s (PNot p)                 = PNot <$> (go s p)
    go s (PImp p q)               = PImp <$> (go s p) <*> (go s q)
    go s (PIff p q)               = PIff <$> (go s p) <*> (go s q)
    go s (PAll xts p)             = PAll xts <$> (go s p)
    go _ p                        = resolve p

expandRPApp s rp es
  = let su  = mkSubst $ safeZip msg (rtVArgs rp) es
        msg = "expandRPApp: " ++ show (EApp (symbol $ rtName rp) es)
    in subst su $ rtBody rp


makeQualifiers (mod,spec) = inModule mod mkQuals
  where
    mkQuals = mapM resolve $ Ms.qualifiers spec


makeClasses cfg vs (mod,spec) = inModule mod $ mapM mkClass $ Ms.classes spec
  where
    --FIXME: cleanup this code
    mkClass (RClass c ss as ms)
      = do tc  <- lookupGhcTyCon (symbolString $ val c)
           ss' <- mapM (mkSpecType "") ss
           let (dc:_) = tyConDataCons tc
           let αs  = map stringRTyVar as
           let as' = [rVar $ stringTyVar a | a <- as ]
           let ms' = [ (s, rFun (S "") (RCls (show $ val c) (flip RVar top <$> as)) t)
                     | (s, t) <- ms]
           vts <- makeAssumeSpec' cfg vs ms'
           let sts = [(val s, unClass $ val t) | (s, _)    <- ms
                                               | (_, _, t) <- vts]
           let t = RCls (fromJust $ tyConClass_maybe tc) as'
           let dcp = DataConP αs [] ss' sts t
           return ((dc,dcp),vts)
    unClass = snd . bkClass . thd3 . bkUniv

makeHints vs (_,spec) = varSymbols id "Hint" vs $ Ms.decr spec
makeLVars vs (_,spec) = fmap fst <$> (varSymbols id "LazyVar" vs $ [(v, ()) | v <- Ms.lvars spec])

varSymbols :: ([Var] -> [Var]) -> String ->  [Var] -> [(LocSymbol, a)] -> BareM [(Var, a)]
varSymbols f n vs  = concatMapM go
  where lvs        = M.map L.sort $ group [(symbol v, locVar v) | v <- vs]
        symbol  = stringSymbol . dropModuleNames . showPpr
        locVar v   = (getSourcePos v, v)
        go (s, ns) = case M.lookup (val s) lvs of 
                     Just lvs -> return ((, ns) <$> varsAfter f s lvs)
                     Nothing  -> ((:[]).(,ns)) <$> lookupGhcVar (symbolString $ val s)
        msg s      = printf "%s: %s for Undefined Var %s"
                         n (show (loc s)) (show (val s))
      
varsAfter f s lvs 
  | eqList (fst <$> lvs)
  = f (snd <$> lvs)
  | otherwise
  = map snd $ takeEqLoc $ dropLeLoc lvs
  where takeEqLoc xs@((l, _):_) = L.takeWhile ((l==) . fst) xs
        takeEqLoc []            = []
        dropLeLoc               = L.dropWhile ((loc s >) . fst)
        eqList []               = True
        eqList (x:xs)           = all (==x) xs

txRefSort env embs = mapBot (addSymSort embs env)

addSymSort embs tcenv (RApp rc@(RTyCon c _ _) ts rs r) 
  = RApp rc ts (addSymSortRef <$> zip ps rs) r
  where ps = rTyConPs $ appRTyCon embs tcenv rc ts
addSymSort _ _ t 
  = t

addSymSortRef (p, RPoly s (RVar v r)) | isDummy v
  = RPoly (safeZip "addRefSortPoly" (fst <$> s) (fst3 <$> pargs p)) t
  where t = ofRSort (ptype p) `strengthen` r
addSymSortRef (p, RPoly s t) 
  = RPoly (safeZip "addRefSortPoly" (fst <$> s) (fst3 <$> pargs p)) t

addSymSortRef (p, RMono s r@(U _ (Pr [up]))) 
  = RMono (safeZip "addRefSortMono" (snd3 <$> pargs up) (fst3 <$> pargs p)) r
addSymSortRef (p, RMono s t)
  = RMono s t

varMeasures vars  = [ (symbol v, varSpecType v) 
                    | v <- vars
                    , isDataConWorkId v
                    , isSimpleType $ varType v
                    ]

varSpecType v      = Loc (getSourcePos v) (ofType $ varType v)


isSimpleType t = null tvs && isNothing (splitFunTy_maybe tb)
  where (tvs, tb) = splitForAllTys t 
-------------------------------------------------------------------------------
-- Renaming Type Variables in Haskell Signatures ------------------------------
-------------------------------------------------------------------------------

-- This throws an exception if there is a mismatch
-- renameTyVars :: (Var, SpecType) -> (Var, SpecType)
renameTyVars (x, lt@(Loc l t))
  | length as == length αs = (x, Loc l $ mkUnivs (rTyVar <$> αs) [] t')
  | otherwise              = Ex.throw  $ err 
  where 
    t'                     = subts su (mkUnivs [] ps tbody)
    su                     = [(y, rTyVar x) | (x, y) <- tyvsmap]
    tyvsmap                = vmap $ execState (mapTyVars τbody tbody) initvmap 
    initvmap               = initMapSt αs as err
    (αs, τbody)            = splitForAllTys $ expandTypeSynonyms $ varType x
    (as, ps, tbody)        = bkUniv t
    err                    = errTypeMismatch x lt


data MapTyVarST = MTVST { τvars  :: S.HashSet Var
                        , tvars  :: S.HashSet RTyVar
                        , vmap   :: [(Var, RTyVar)] 
                        , errmsg :: Error 
                        }

initMapSt α a  = MTVST (S.fromList α) (S.fromList a) []

mapTyVars :: (PPrint r, Reftable r) => Type -> RRType r -> State MapTyVarST ()
mapTyVars τ (RAllT a t)   
  = do modify $ \s -> s{ tvars = S.delete a (tvars s) }
       mapTyVars τ t 
mapTyVars (ForAllTy α τ) t 
  = do modify $ \s -> s{ τvars = S.delete α (τvars s) }
       mapTyVars τ t 
mapTyVars (FunTy τ τ') (RFun _ t t' _) 
   = mapTyVars τ t  >> mapTyVars τ' t'
mapTyVars (TyConApp _ τs) (RApp _ ts _ _) 
   = zipWithM_ mapTyVars τs ts
mapTyVars (TyVarTy α) (RVar a _)      
   = modify $ \s -> mapTyRVar α a s
mapTyVars τ (RAllP _ t)   
  = mapTyVars τ t 
mapTyVars τ (RCls _ ts)     
  = return ()
mapTyVars τ (RAllE _ _ t)   
  = mapTyVars τ t 
mapTyVars τ (REx _ _ t)
  = mapTyVars τ t 
mapTyVars τ (RExprArg _)
  = return ()
mapTyVars (AppTy τ τ') (RAppTy t t' _) 
  = do  mapTyVars τ t 
        mapTyVars τ' t' 
mapTyVars τ t               
  = Ex.throw =<< errmsg <$> get
       -- errorstar $ "Bare.mapTyVars : " ++ err

mapTyRVar α a s@(MTVST αs as αas err)
  | (α `S.member` αs) && (a `S.member` as)
  = MTVST (S.delete α αs) (S.delete a as) ((α, a):αas) err
  | (not (α `S.member` αs)) && (not (a `S.member` as))
  = s
  | otherwise
  = Ex.throw err -- errorstar err

mkVarExpr v 
  | isDataConWorkId v && not (null tvs) && isNothing tfun
  = EApp (dataConSymbol (idDataCon v)) []         
  | otherwise   
  = EVar $ symbol v
  where t            = varType v
        (tvs, tbase) = splitForAllTys t
        tfun         = splitFunTy_maybe tbase

subsFreeSymbols su  = tx
  where 
    tx              = fmap $ mapSnd $ subst su 

subsFreeSymbolsQual su = tx
  where
    tx              = fmap $ mapBody $ subst su
    mapBody f (Q n p b) = Q n p (f b)

-- meetDataConSpec :: [(Var, SpecType)] -> [(DataCon, DataConP)] -> [(Var, SpecType)]
meetDataConSpec xts dcs  = M.toList $ L.foldl' upd dcm xts 
  where 
    dcm                  = M.fromList $ dataConSpec dcs
    upd dcm (x, t)       = M.insert x (maybe t (meetPad t) (M.lookup x dcm)) dcm
    strengthen (x,t)     = (x, maybe t (meetPad t) (M.lookup x dcm))


-- dataConSpec :: [(DataCon, DataConP)] -> [(Var, SpecType)]
dataConSpec :: [(DataCon, DataConP)]-> [(Var, (RType Class RTyCon RTyVar RReft))]
dataConSpec dcs = concatMap mkDataConIdsTy [(dc, dataConPSpecType dc t) | (dc, t) <- dcs]

meetPad t1 t2 = -- traceShow ("meetPad: " ++ msg) $
  case (bkUniv t1, bkUniv t2) of
    ((_, π1s, _), (α2s, [], t2')) -> meet t1 (mkUnivs α2s π1s t2')
    ((α1s, [], t1'), (_, π2s, _)) -> meet (mkUnivs α1s π2s t1') t2
    _                             -> errorstar $ "meetPad: " ++ msg
  where msg = "\nt1 = " ++ showpp t1 ++ "\nt2 = " ++ showpp t2
 
------------------------------------------------------------------
---------- Error-Reader-IO For Bare Transformation ---------------
------------------------------------------------------------------

type BareM a = WriterT [Warn] (ErrorT String (StateT BareEnv IO)) a

type Warn    = String

data BareEnv = BE { modName  :: !ModName
                  , tcEnv    :: !(M.HashMap TyCon RTyCon)
                  , rtEnv    :: !RTEnv
                  , varEnv   :: ![(Symbol,Var)]
                  , hscEnv   :: HscEnv }

setModule m b = b { modName = m }

inModule m act = do
  old <- gets modName
  modify $ setModule m
  res <- act
  modify $ setModule old
  return res

withVArgs vs act = do
  old <- gets rtEnv
  mapM (mkExprAlias . showpp) vs
  res <- act
  modify $ \be -> be { rtEnv = old }
  return res

addSym x = modify $ \be -> be { varEnv = (varEnv be) `L.union` [x] }

mkExprAlias v
  = setRTAlias v (Right (RTA v [] [] (RExprArg (EVar $ symbol v)) dummyPos))

setRTAlias s a =
  modify $ \b -> b { rtEnv = mapRT (M.insert s a) $ rtEnv b }

setRPAlias s a =
  modify $ \b -> b { rtEnv = mapRP (M.insert s a) $ rtEnv b }

execBare :: BareM a -> BareEnv -> IO a
execBare act benv = 
   do z <- evalStateT (runErrorT (runWriterT act)) benv
      case z of
        Left s        -> errorstar $ "execBare:\n " ++ s
        Right (x, ws) -> do forM_ ws $ putStrLn . ("WARNING: " ++) 
                            return x

wrapErr msg f x = yesStack 
  where
    noStack     = f x
    yesStack    = noStack `catchError` \e -> throwError $ str e
    str e       = printf "Bare Error %s: \nThrows Exception: %s\n" msg e

------------------------------------------------------------------
------------------- API: Bare Refinement Types -------------------
------------------------------------------------------------------

makeMeasureSpec (mod,spec) = inModule mod mkSpec
  where
    mkSpec = mkMeasureDCon =<< wrapErr "mkMeasureSort" mkMeasureSort =<< m
    m      = Ms.mkMSpec <$> (mapM expandRTAliasMeasure $ Ms.measures spec)
                        <*> return (Ms.cmeasures spec)
                        <*> (mapM expandRTAliasMeasure $ Ms.imeasures spec)

makeMeasureSpec' = mapFst (mapSnd uRType <$>) . Ms.dataConTypes . first (mapReft ur_reft)

makeClassMeasureSpec (Ms.MSpec {..}) = tx <$> M.elems cmeasMap
  where
    tx (M n s _) = (n, CM n (mapReft ur_reft s) -- [(t,m) | (IM n' t m) <- imeas, n == n']
                   )

makeTargetVars :: ModName -> [Var] -> [String] -> BareM [Var]
makeTargetVars name vs ss = do
  env <- gets hscEnv
  ns <- liftIO $ catMaybes <$> mapM (lookupName env name) (map prefix ss)
  return $ filter ((`elem` ns) . varName) vs
 where
  prefix s = getModString name ++ "." ++ s


makeAssumeSpec cmod cfg vs lvs (mod,spec)
  |  cmod == mod
  = makeLocalAssumeSpec cfg cmod vs lvs $ Ms.sigs spec
  | otherwise 
  = inModule mod $ makeAssumeSpec' cfg vs $ Ms.sigs spec

makeLocalAssumeSpec :: Config -> ModName -> [Var] -> [Var] -> [(LocSymbol, BareType)]
                    -> BareM [(ModName, Var, Located SpecType)]
 
makeLocalAssumeSpec cfg mod vs lvs xbs
  = do env     <- get
       vbs1    <- fmap expand3 <$> varSymbols fchoose "Var" lvs (dupSnd <$> xbs1)
       when (not $ noCheckUnknown cfg) $
         checkDefAsserts env vbs1 xbs1
       vts1    <- map (addFst3 mod) <$> mapM mkVarSpec vbs1
       vts2    <- makeAssumeSpec' cfg vs xbs2
       return   $ vts1 ++ vts2
  where (xbs1, xbs2)  = L.partition (modElem mod . fst) xbs

        dupSnd (x, y)       = (dropMod x, (x, y))
        expand3 (x, (y, w)) = (x, y, w)

        dropMod  = fmap (stringSymbol . dropModuleNames . symbolString)

        fchoose ls = maybe ls (:[]) $ L.find (`elem` vs) ls

        modElem n x = (takeModuleNames $ show $ val x) == (show n)

makeAssumeSpec' :: Config -> [Var] -> [(LocSymbol, BareType)]
                -> BareM [(ModName, Var, Located SpecType)]
makeAssumeSpec' cfg vs xbs
  = do vbs <- map (joinVar vs) <$> lookupIds xbs
       env@(BE { modName = mod}) <- get
       when (not $ noCheckUnknown cfg) $
         checkDefAsserts env vbs xbs
       map (addFst3 mod) <$> mapM mkVarSpec vbs

-- the Vars we lookup in GHC don't always have the same tyvars as the Vars
-- we're given, so return the original var when possible.
-- see tests/pos/ResolvePred.hs for an example
joinVar vs (v,s,t) = case L.find ((== showPpr v) . showPpr) vs of
                       Just v' -> (v',s,t)
                       Nothing -> (v,s,t)

lookupIds xs = mapM lookup xs
  where
    lookup (s, t) = (,s,t) <$> lookupGhcVar (ss s)
    ss = symbolString . symbol

checkDefAsserts :: BareEnv -> [(Var, LocSymbol, BareType)] -> [(LocSymbol, BareType)] -> BareM ()
checkDefAsserts env vbs xbs   = applyNonNull (return ()) grumble  undefSigs
  where
    undefSigs                 = [x | (x, _) <- assertSigs, not (x `S.member` definedSigs)]
    assertSigs                = filter isTarget xbs
    definedSigs               = S.fromList $ snd3 <$> vbs
    grumble xs                = mapM_ (warn . berrUnknownVar) xs -- [berrUnknownVar (loc x) (val x) | x <- xs] 
    moduleName                = getModString $ modName env
    isTarget                  = L.isPrefixOf moduleName . symbolStringRaw . val . fst
    symbolStringRaw           = stripParens . symbolString

    -- grumble                   = {- throwError -} warn . render . vcat . fmap errorMsg
    -- errorMsg                  = (text "Specification for unknown variable:" <+>) . locatedSymbolText
 

warn x = tell [x]





mkVarSpec                 :: (Var, LocSymbol, BareType) -> BareM (Var, Located SpecType)
mkVarSpec (v, Loc l _, b) = ((v, ) . (Loc l) . generalize) <$> mkSpecType msg b
  where 
    msg                   = berrVarSpec l v b



showTopLevelVars vs = 
  forM vs $ \v -> 
    if isExportedId v 
      then donePhase Loud ("Exported: " ++ showPpr v)
      else return ()

----------------------------------------------------------------------

makeTyConEmbeds (mod,spec)
  = inModule mod $ makeTyConEmbeds' $ Ms.embeds spec

makeTyConEmbeds' :: TCEmb (Located String) -> BareM (TCEmb TyCon)
makeTyConEmbeds' z = M.fromList <$> mapM tx (M.toList z)
  where 
    tx (c, y) = (, y) <$> lookupGhcTyCon' c --  wrapErr () (lookupGhcTyCon (val c))
     

lookupGhcTyCon' c = wrapErr msg lookupGhcTyCon (val c)
  where 
    msg :: String = berrUnknownTyCon c


makeLazies (mod,spec)
  = inModule mod $ makeLazies' $ Ms.lazy spec

makeLazies' :: S.HashSet Symbol -> BareM (S.HashSet Var)
makeLazies' s = S.fromList <$> (fmap fst3 <$> lookupIds xxs)
  where xs  = S.toList s
        xxs = zip xs xs


makeInvariants (mod,spec)
  = inModule mod $ makeInvariants' $ Ms.invariants spec

makeInvariants' :: [Located BareType] -> BareM [Located SpecType]
makeInvariants' ts = mapM mkI ts
  where 
    mkI (Loc l t)      = (Loc l) . generalize <$> mkSpecType (berrInvariant l t) t

mkSpecType msg t = mkSpecType' msg (snd3 $ bkUniv t)  t

mkSpecType' :: String -> [PVar BSort] -> BareType -> BareM SpecType
mkSpecType' msg πs = expandRTAlias . txParams subvUReft (uPVar <$> πs)

makeSymbols vs xs' xts yts = mkxvs
  where
    xs''  = val <$> xs'
    zs    = (concatMap freeSymbols ((snd <$> xts))) `sortDiff` xs''
    zs'   = (concatMap freeSymbols ((snd <$> yts))) `sortDiff` xs''
    xs    = sortNub $ zs ++ zs'
    mkxvs = do
      svs <- gets varEnv
      return [(x,v') | (x,v) <- svs, x `elem` xs, let (v',_,_) = joinVar vs (v,x,x)]

freeSymbols ty = sortNub $ concat $ efoldReft (\_ _ -> []) (\ _ -> ()) f emptySEnv [] (val ty)
  where 
    f γ _ r xs = let Reft (v, _) = toReft r in 
                 [ x | x <- syms r, x /= v, not (x `memberSEnv` γ)] : xs

-----------------------------------------------------------------
------ Querying GHC for Id, Type, Class, Con etc. ---------------
-----------------------------------------------------------------

class GhcLookup a where
  lookupName :: HscEnv -> ModName -> a -> IO (Maybe Name)
  candidates :: a -> [a]
  pp         :: a -> String 

instance GhcLookup String where
  lookupName     = stringLookup
  candidates x   = [x]
  pp         x   = x

instance GhcLookup Name where
  lookupName _ _ = return . Just
  candidates x   = [x]
  pp             = showPpr 

lookupGhcThing :: (GhcLookup a) => String -> (TyThing -> Maybe b) -> a -> BareM b
lookupGhcThing name f x 
  = do zs <- catMaybes <$> mapM (lookupGhcThing' name f) (candidates x)
       case zs of 
         x:_ -> return x
         _   -> throwError $ "lookupGhcThing unknown " ++ name ++ " : " ++ (pp x)

lookupGhcThing' :: (GhcLookup a) => String -> (TyThing -> Maybe b) -> a -> BareM (Maybe b)
lookupGhcThing' _    f x 
  = do (BE mod _ _ _ env) <- get
       z              <- liftIO $ lookupName env mod x
       case z of
         Nothing -> return Nothing 
         Just n  -> liftIO $ liftM (join . (f <$>) . snd) (tcRnLookupName env n)

stringLookup :: HscEnv -> ModName -> String -> IO (Maybe Name)
stringLookup env mod k
  | k `M.member` wiredIn
  = return $ M.lookup k wiredIn
  | otherwise
  = stringLookupEnv env mod k

stringLookupEnv env mod s
  | isSrcImport mod
  = do let modName = getModName mod
       L _ rn <- hscParseIdentifier env s
       res    <- lookupRdrName env modName rn
       case res of
         Just _  -> return res
         Nothing -> lookupRdrName env modName (setRdrNameSpace rn tcName)
  | otherwise
  = do L _ rn         <- hscParseIdentifier env s
       (_, lookupres) <- tcRnLookupRdrName env rn
       case lookupres of
         Just (n:_) -> return (Just n)
         _          -> return Nothing

-- | lookupGhcVar: It's possible that we have already resolved the Name we are
--   looking for, but have had to turn it back into a String, e.g. to be used in
--   an Expr, as in {v:Ordering | v = EQ}. In this case, the fully-qualified Name
--   (GHC.Types.EQ) will likely not be in scope, so we store our own mapping of
--   fully-qualified Names to Vars and prefer pulling Vars from it.
  
lookupGhcVar :: GhcLookup a => a -> BareM Var
lookupGhcVar x
  = do env <- gets varEnv
       case L.lookup (symbol $ pp x) env of
         Nothing -> lookupGhcThing "Var" fv x
         Just v  -> return v
  where
    fv (AnId x)     = Just x
    fv (ADataCon x) = Just $ dataConWorkId x
    fv _            = Nothing

lookupGhcTyCon       ::  GhcLookup a => a -> BareM TyCon
lookupGhcTyCon s     = (lookupGhcThing "TyCon" ftc s) `catchError` (tryPropTyCon s)
  where 
    ftc (ATyCon x)   = Just x
    ftc (ADataCon x) = Just $ dataConTyCon x
    ftc _            = Nothing

tryPropTyCon s e   
  | pp s == propConName = return propTyCon 
  | otherwise           = throwError e

lookupGhcClass       = lookupGhcThing "Class" ftc 
  where 
    ftc (ATyCon x)   = tyConClass_maybe x 
    ftc _            = Nothing

lookupGhcDataCon dc  = case isTupleDC dc of 
                         Just n  -> return $ tupleCon BoxedTuple n
                         Nothing -> lookupGhcDataCon' dc 

isTupleDC zs@('(':',':_) = Just $ length zs - 1
isTupleDC _              = Nothing


lookupGhcDataCon'    = lookupGhcThing "DataCon" fdc
  where 
    fdc (ADataCon x) = Just x
    fdc _            = Nothing

wiredIn :: M.HashMap String Name
wiredIn = M.fromList $ {- tracePpr "wiredIn: " $ -} special ++ wiredIns 
  where wiredIns = [ (showPpr n, n) | thing <- wiredInThings, let n = getName thing ]
        special  = [ ("GHC.Integer.smallInteger", smallIntegerName)
                   , ("GHC.Num.fromInteger"     , fromIntegerName ) ]


fixpointPrims = ["Pred", "Prop", "List", "Set_Set", "Set_sng", "Set_cup", "Set_cap"
                ,"Set_dif", "Set_emp", "Set_mem", "Set_sub", "VV"]

class Resolvable a where
  resolve :: a -> BareM a

instance Resolvable Qualifier where
  resolve (Q n ps b) = Q n <$> mapM (secondM resolve) ps <*> resolve b

instance Resolvable Pred where
  resolve (PAnd ps)       = PAnd <$> mapM resolve ps
  resolve (POr  ps)       = POr  <$> mapM resolve ps
  resolve (PNot p)        = PNot <$> resolve p
  resolve (PImp p q)      = PImp <$> resolve p <*> resolve q
  resolve (PIff p q)      = PIff <$> resolve p <*> resolve q
  resolve (PBexp b)       = PBexp <$> resolve b
  resolve (PAtom r e1 e2) = PAtom r <$> resolve e1 <*> resolve e2
  resolve (PAll vs p)     = PAll <$> mapM (secondM resolve) vs
                                 <*> resolve p
  resolve p               = return p

instance Resolvable Expr where
  resolve (EVar s)       = EVar <$> resolve s
  resolve (EApp s es)    = EApp <$> resolve s <*> es'
      where es'          = mapM resolve es
  resolve (EBin o e1 e2) = EBin o <$> resolve e1 <*> resolve e2
  resolve (EIte p e1 e2) = EIte <$> resolve p <*> resolve e1 <*> resolve e2
  resolve (ECst x s)     = ECst <$> resolve x <*> resolve s
  resolve x              = return x

instance Resolvable Symbol where
  resolve (S s)
      | s `elem` fixpointPrims = return (S s)
      | otherwise = do env <- gets (typeAliases.rtEnv)
                       case M.lookup s env of
                         Nothing | isCon s
                           -> do v <- lookupGhcVar s
                                 let qs = symbol $ showPpr v
                                 addSym (qs,v)
                                 return qs
                         _ -> return (S s)

instance Resolvable Sort where
  resolve FInt         = return FInt
  resolve FNum         = return FNum
  resolve s@(FObj _)   = return s --FObj . S <$> lookupName env m s
  resolve s@(FVar _)   = return s
  resolve (FFunc i ss) = FFunc i <$> mapM resolve ss
  resolve (FApp tc ss)
      | tcs `elem` fixpointPrims = FApp tc <$> ss'
      | otherwise     = FApp <$> (stringFTycon.showPpr <$> lookupGhcTyCon tcs)
                             <*> ss'
      where tcs = fTyconString tc
            ss' = mapM resolve ss

instance Resolvable (UReft Reft) where
  resolve (U r p) = U <$> resolve r <*> resolve p

instance Resolvable Reft where
  resolve (Reft (s, ras)) = Reft . (s,) <$> mapM resolveRefa ras
    where
      resolveRefa (RConc p) = RConc <$> resolve p
      resolveRefa kv        = return kv

instance Resolvable Predicate where
  resolve (Pr pvs) = Pr <$> mapM resolve pvs

instance (Resolvable t) => Resolvable (PVar t) where
  resolve (PV n t as) = PV n t <$> mapM (third3M resolve) as

instance Resolvable () where
  resolve () = return ()

isCon (c:cs) = isUpper c
isCon []     = False

--------------------------------------------------------------------
------ Predicate Types for WiredIns --------------------------------
--------------------------------------------------------------------

maxArity :: Arity 
maxArity = 7

wiredTyDataCons :: ([(TyCon, TyConP)] , [(DataCon, DataConP)])
wiredTyDataCons = (concat tcs, concat dcs)
  where 
    (tcs, dcs)  = unzip l
    l           = [listTyDataCons] ++ map tupleTyDataCons [1..maxArity]

listTyDataCons :: ([(TyCon, TyConP)] , [(DataCon, DataConP)])
listTyDataCons   = ( [(c, TyConP [(RTV tyv)] [p] [0] [] (Just fsize))]
                   , [(nilDataCon , DataConP [(RTV tyv)] [p] [] [] lt)
                   , (consDataCon, DataConP [(RTV tyv)] [p] [] cargs  lt)])
    where c      = listTyCon
          [tyv]  = tyConTyVars c
          t      = {- TyVarTy -} rVar tyv :: RSort
          fld    = stringSymbol "fld"
          x      = stringSymbol "x"
          xs     = stringSymbol "xs"
          p      = PV (stringSymbol "p") t [(t, fld, EVar fld)]
          px     = (pdVarReft $ PV (stringSymbol "p") t [(t, fld, EVar x)]) 
          lt     = rApp c [xt] [RMono [] $ pdVarReft p] top                 
          xt     = rVar tyv
          xst    = rApp c [RVar (RTV tyv) px] [RMono [] $ pdVarReft p] top  
          cargs  = [(xs, xst), (x, xt)]
          fsize  = \x -> EApp (S "len") [EVar x] 

tupleTyDataCons :: Int -> ([(TyCon, TyConP)] , [(DataCon, DataConP)])
tupleTyDataCons n = ( [(c, TyConP (RTV <$> tyvs) ps [0..(n-2)] [] Nothing)]
                    , [(dc, DataConP (RTV <$> tyvs) ps []  cargs  lt)])
  where c             = tupleTyCon BoxedTuple n
        dc            = tupleCon BoxedTuple n 
        tyvs@(tv:tvs) = tyConTyVars c
        (ta:ts)       = (rVar <$> tyvs) :: [RSort]
        flds          = mks "fld"
        fld           = stringSymbol "fld"
        x1:xs         = mks "x"
        -- y             = stringSymbol "y"
        ps            = mkps pnames (ta:ts) ((fld, EVar fld):(zip flds (EVar <$>flds)))
        ups           = uPVar <$> ps
        pxs           = mkps pnames (ta:ts) ((fld, EVar x1):(zip flds (EVar <$> xs)))
        lt            = rApp c (rVar <$> tyvs) (RMono [] . pdVarReft <$> ups) top
        xts           = zipWith (\v p -> RVar (RTV v) (pdVarReft p)) tvs pxs
        cargs         = reverse $ (x1, rVar tv) : (zip xs xts)
        pnames        = mks_ "p"
        mks  x        = (\i -> stringSymbol (x++ show i)) <$> [1..n]
        mks_ x        = (\i ->  (x++ show i)) <$> [2..n]


pdVarReft = U top . pdVar 

mkps ns (t:ts) ((f,x):fxs) = reverse $ mkps_ (stringSymbol <$> ns) ts fxs [(t, f, x)] [] 
mkps _  _      _           = error "Bare : mkps"

mkps_ []     _       _          _    ps = ps
mkps_ (n:ns) (t:ts) ((f, x):xs) args ps
  = mkps_ ns ts xs (a:args) (p:ps)
  where p = PV n t args
        a = (t, f, x)
mkps_ _     _       _          _    _ = error "Bare : mkps_"

------------------------------------------------------------------------
----------------- Transforming Raw Strings using GHC Env ---------------
------------------------------------------------------------------------

-- makeRTyConPs :: Reftable r => String -> M.HashMap TyCon RTyCon -> [RPVar] -> RRType r -> RRType r
-- makeRTyConPs msg tyi πs t@(RApp c ts rs r) 
--   | null $ rTyConPs c
--   = expandRApp tyi t
--   | otherwise 
--   = RApp c {rTyConPs = findπ πs <$> rTyConPs c} ts rs r 
--   -- need type application????
--   where findπ πs π = findWithDefaultL (== π) πs (emsg π)
--         emsg π     = errorstar $ "Bare: out of scope predicate " ++ msg ++ " " ++ show π
-- --             throwError $ "Bare: out of scope predicate" ++ show π 
-- 
-- 
-- makeRTyConPs _ _ _ t = t


ofBareType' :: (PPrint r, Reftable r) => String -> BRType r -> BareM (RRType r)
ofBareType' msg = wrapErr msg ofBareType

ofBareType :: (PPrint r, Reftable r) => BRType r -> BareM (RRType r)
ofBareType (RVar a r) 
  = return $ RVar (stringRTyVar a) r
ofBareType (RFun x t1 t2 _) 
  = liftM2 (rFun x) (ofBareType t1) (ofBareType t2)
ofBareType t@(RAppTy t1 t2 r) 
  = liftM3 (\t1 t2 r -> traceShow ("RAPPTY: " ++ show t) $ RAppTy t1 t2 r) (ofBareType t1) (ofBareType t2) (return r)
ofBareType (RAllE x t1 t2)
  = liftM2 (RAllE x) (ofBareType t1) (ofBareType t2)
ofBareType (REx x t1 t2)
  = liftM2 (REx x) (ofBareType t1) (ofBareType t2)
ofBareType (RAllT a t) 
  = liftM  (RAllT (stringRTyVar a)) (ofBareType t)
ofBareType (RAllP π t) 
  = liftM2 RAllP (ofBPVar π) (ofBareType t)
ofBareType (RApp tc ts@[_] rs r) 
  | isList tc
  = do tyi <- tcEnv <$> get
       liftM2 (bareTCApp tyi r listTyCon) (mapM ofRef rs) (mapM ofBareType ts)
ofBareType (RApp tc ts rs r) 
  | isTuple tc
  = do tyi <- tcEnv <$> get
       liftM2 (bareTCApp tyi r c) (mapM ofRef rs) (mapM ofBareType ts)
    where c = tupleTyCon BoxedTuple (length ts)
ofBareType (RApp tc ts rs r) 
  = do tyi <- tcEnv <$> get
       liftM3 (bareTCApp tyi r) (lookupGhcTyCon tc) (mapM ofRef rs) (mapM ofBareType ts)
ofBareType (RCls c ts)
  = liftM2 RCls (lookupGhcClass c) (mapM ofBareType ts)
ofBareType (ROth s)
  = return $ ROth s
ofBareType t
  = errorstar $ "Bare : ofBareType cannot handle " ++ show t

ofRef (RPoly ss t)   
  = liftM2 RPoly (mapM ofSyms ss) (ofBareType t)
ofRef (RMono ss r) 
  = liftM (`RMono` r) (mapM ofSyms ss)

ofSyms (x, t)
  = liftM ((,) x) (ofBareType t)

-- TODO: move back to RefType
bareTCApp _ r c rs ts | length ts == tyConArity c
  = if isTrivial t0 then t' else t
    where t0 = rApp c ts rs top
          t  = rApp c ts rs r
          t' = (expandRTypeSynonyms t0) `strengthen` r
-- otherwise create an error
-- create the error later to get better message
bareTCApp _ _ c rs ts = rApp c ts rs top

expandRTypeSynonyms = ofType . expandTypeSynonyms . toType

stringRTyVar  = rTyVar . stringTyVar 
-- stringTyVarTy = TyVarTy . stringTyVar

mkMeasureDCon :: Ms.MSpec t Symbol -> BareM (Ms.MSpec t DataCon)
mkMeasureDCon m = (forM (measureCtors m) $ \n -> (n,) <$> lookupGhcDataCon n)
                  >>= (return . mkMeasureDCon_ m)

mkMeasureDCon_ :: Ms.MSpec t Symbol -> [(String, DataCon)] -> Ms.MSpec t DataCon
mkMeasureDCon_ m ndcs = m' {Ms.ctorMap = cm'}
  where 
    m'  = fmap tx m
    cm' = hashMapMapKeys (tx' . tx) $ Ms.ctorMap m'
    tx  = mlookup (M.fromList ndcs) . symbolString
    tx' = dataConSymbol

measureCtors ::  Ms.MSpec t Symbol -> [String]
measureCtors = sortNub . fmap (symbolString . ctor) . concat . M.elems . Ms.ctorMap

-- mkMeasureSort :: (PVarable pv, Reftable r) => Ms.MSpec (BRType pv r) bndr-> BareM (Ms.MSpec (RRType pv r) bndr)
mkMeasureSort (Ms.MSpec c m cm im)
  = Ms.MSpec c <$> forM m tx <*> forM cm tx <*> forM im tx
    where
      msg m = berrMeasure (loc $ name m) (name m) (sort m)
      tx  m = liftM (\s' -> m {sort = s'}) (ofBareType' (msg m) (sort m))



-----------------------------------------------------------------------
----------------------- Prop TyCon Definition -------------------------
-----------------------------------------------------------------------

propTyCon   = stringTyCon 'w' 24 propConName
-- propMeasure = (stringSymbolRaw propConName, FFunc  

-----------------------------------------------------------------------
---------------- Bare Predicate: DataCon Definitions ------------------
-----------------------------------------------------------------------

makeConTypes (name,spec) = inModule name $ makeConTypes' $ Ms.dataDecls spec

makeConTypes' :: [DataDecl] -> BareM ([(TyCon, TyConP)], [[(DataCon, DataConP)]])
makeConTypes' dcs = unzip <$> mapM ofBDataDecl dcs

ofBDataDecl :: DataDecl -> BareM ((TyCon, TyConP), [(DataCon, DataConP)])
ofBDataDecl (D tc as ps cts pos sfun)
  = do πs    <- mapM ofBPVar ps
       tc'   <- lookupGhcTyCon tc
       cts'  <- mapM (ofBDataCon (berrDataDecl pos tc πs) tc' αs ps πs) cts
       let tys     = [t | (_, dcp) <- cts', (_, t) <- tyArgs dcp]
       let initmap = zip (uPVar <$> πs) [0..]
       let varInfo = concatMap (getPsSig initmap True) tys
       let cov     = [i | (i, b)<- varInfo, b, i >=0]
       let contr   = [i | (i, b)<- varInfo, not b, i >=0]
       return ((tc', TyConP αs πs cov contr sfun), cts')
    where αs   = fmap (RTV . stringTyVar) as
          -- cpts = fmap (second (fmap (second (mapReft ur_pred)))) cts

getPsSig m pos (RAllT _ t) 
  = getPsSig m pos t
getPsSig m pos (RApp _ ts rs r) 
  = addps m pos r ++ concatMap (getPsSig m pos) ts 
    ++ concatMap (getPsSigPs m pos) rs
getPsSig m pos (RVar _ r) 
  = addps m pos r
getPsSig m pos (RAppTy t1 t2 r) 
  = addps m pos r ++ getPsSig m pos t1 ++ getPsSig m pos t2
getPsSig m pos (RFun _ t1 t2 r) 
  = addps m pos r ++ getPsSig m pos t2 ++ getPsSig m (not pos) t1


getPsSigPs m pos (RMono _ r) = addps m pos r
getPsSigPs m pos (RPoly _ t) = getPsSig m pos t

addps m pos (U _ ps) = (flip (,)) pos . f  <$> pvars ps
  where f = fromMaybe (error "Bare.addPs: notfound") . (`L.lookup` m) . uPVar
-- ofBPreds = fmap (fmap stringTyVarTy)
dataDeclTyConP d 
  = do let αs = fmap (RTV . stringTyVar) (tycTyVars d)  -- as
       πs    <- mapM ofBPVar (tycPVars d)               -- ps
       tc'   <- lookupGhcTyCon (tycName d)              -- tc 
       return $ (tc', TyConP αs πs)

-- ofBPreds = fmap (fmap stringTyVarTy)
ofBPVar :: PVar BSort -> BareM (PVar RSort)
ofBPVar = mapM_pvar ofBareType 

mapM_pvar :: (Monad m) => (a -> m b) -> PVar a -> m (PVar b)
mapM_pvar f (PV x t txys) 
  = do t'    <- f t
       txys' <- mapM (\(t, x, y) -> liftM (, x, y) (f t)) txys 
       return $ PV x t' txys'

ofBDataCon msg tc αs ps πs (c, xts)
  = do c'      <- wrapErr msg lookupGhcDataCon c
       ts'     <- mapM (mkSpecType' msg ps) ts
       let cs   = map ofType (dataConStupidTheta c')
       let t0   = rApp tc rs (RMono [] . pdVarReft <$> πs) top 
       return   $ (c', DataConP αs πs cs (reverse (zip xs' ts')) t0)
    where 
       (xs, ts) = unzip xts
       xs'      = map stringSymbol xs
       rs       = [rVar α | RTV α <- αs] -- [RVar α pdTrue | α <- αs]

-----------------------------------------------------------------------
---------------- Bare Predicate: RefTypes -----------------------------
-----------------------------------------------------------------------

txParams f πs t = mapReft (f (txPvar (predMap πs t))) t

txPvar :: M.HashMap Symbol UsedPVar -> UsedPVar -> UsedPVar 
txPvar m π = π { pargs = args' }
  where args' | not (null (pargs π)) = zipWith (\(_,x ,_) (t,_,y) -> (t, x, y)) (pargs π') (pargs π)
              | otherwise            = pargs π'
        π'    = fromMaybe (errorstar err) $ M.lookup (pname π) m
        err   = "Bare.replaceParams Unbound Predicate Variable: " ++ show π

predMap πs t = Ex.assert (M.size xπm == length xπs) xπm 
  where xπm = M.fromList xπs
        xπs = [(pname π, π) | π <- πs ++ rtypePredBinds t]

rtypePredBinds = map uPVar . snd3 . bkUniv

-- rtypePredBinds t = everything (++) ([] `mkQ` grab) t
--   where grab ((RAllP pv _) :: BRType RPVar RPredicate) = [pv]
--         grab _                                         = []

----------------------------------------------------------------------------------------------
----- Checking GhcSpec -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------

checkGhcSpec :: (GhcSpec, [Measure SpecType DataCon]) -> Either [Error] GhcSpec

checkGhcSpec (sp, ms) =  applyNonNull (Right sp) Left errors
  where 
    errors           =  mapMaybe (checkBind "variable"    emb env) (tySigs     sp)
                     ++ mapMaybe (checkBind "constructor" emb env) (dcons      sp)
                     ++ mapMaybe (checkBind "measure"     emb env) (measSpec   sp)
                     ++ mapMaybe (checkInv  emb env)               (invariants sp)
                     ++ checkMeasures emb env ms
                     ++ mapMaybe checkMismatch                     (tySigs     sp)
                     ++ checkDuplicate                             (tySigs     sp)
    dcons spec       =  mapSnd (Loc dummyPos) <$> dataConSpec (dconsP spec) 
    emb              =  tcEmbeds sp
    env              =  ghcSpecEnv sp
    measSpec sp      =  [(x, uRType <$> t) | (x, t) <- meas sp] 

-- specError            = errorstar 
--                      . render 
--                      . vcat 
--                      . punctuate (text "\n----\n") 
--                      . (text "Alas, errors found in specification..." :)

checkInv :: TCEmb TyCon -> SEnv SortedReft -> Located SpecType -> Maybe Error
checkInv emb env t   = checkTy err emb env (val t) 
  where 
    err              = ErrInvt (sourcePosSrcSpan $ loc t) (val t)


checkBind :: (PPrint v) => String -> TCEmb TyCon -> SEnv SortedReft -> (v, Located SpecType) -> Maybe Error 
checkBind s emb env (v, Loc l t) = checkTy msg emb env t
  where 
    msg = ErrTySpec (sourcePosSrcSpan l) (text s <+> pprint v) t 

checkTy :: (Doc -> Error) -> TCEmb TyCon -> SEnv SortedReft -> SpecType -> Maybe Error
checkTy mkE emb env t = mkE <$> checkRType emb env t

checkDuplicate       :: [(Var, Located SpecType)] -> [Error]
checkDuplicate xts   = mkErr <$> dups
  where 
    mkErr (x, ts)    = ErrDupSpecs (getSrcSpan x) (pprint x) (sourcePosSrcSpan . loc <$> ts)
    dups             = [z | z@(x, t1:t2:_) <- M.toList $ group xts ]


checkMismatch        :: (Var, Located SpecType) -> Maybe Error
checkMismatch (x, t) = if ok then Nothing else Just err
  where 
    ok               = tyCompat x (val t)
    err              = errTypeMismatch x t

tyCompat x t         = lhs == rhs
  where 
    lhs :: RSort     = toRSort t
    rhs :: RSort     = ofType $ varType x
    msg              = printf "tyCompat: l = %s r = %s" (showpp lhs) (showpp rhs)

ghcSpecEnv sp        = fromListSEnv binds
  where 
    emb              = tcEmbeds sp
    binds            =  [(x,        rSort t) | (x, Loc _ t) <- meas sp]
                     ++ [(symbol v, rSort t) | (v, Loc _ t) <- ctors sp]
                     ++ [(x,        vSort v) | (x, v) <- freeSyms sp, isConLikeId v]
    rSort            = rTypeSortedReft emb 
    vSort            = rSort . varRType 
    varRType         :: Var -> RRType ()
    varRType         = ofType . varType

errTypeMismatch     :: Var -> Located SpecType -> Error
errTypeMismatch x t = ErrMismatch (sourcePosSrcSpan $ loc t) (pprint x) (varType x) (val t)

-------------------------------------------------------------------------------------
-- | This function checks if a type is malformed in a given environment -------------
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
checkRType :: (PPrint r, Reftable r) => TCEmb TyCon -> SEnv SortedReft -> RRType r -> Maybe Doc 
-------------------------------------------------------------------------------------

checkRType emb env t         = efoldReft cb (rTypeSortedReft emb) f env Nothing t 
  where 
    cb c ts                  = classBinds (RCls c ts)
    f env me r err           = err <|> checkReft env emb me r

checkReft                    :: (PPrint r, Reftable r) => SEnv SortedReft -> TCEmb TyCon -> Maybe (RRType r) -> r -> Maybe Doc 
checkReft env emb Nothing _  = Nothing -- RMono / Ref case, not sure how to check these yet.  
checkReft env emb (Just t) _ = (dr $+$) <$> checkSortedReftFull env r 
  where 
    r                        = rTypeSortedReft emb t
    dr                       = text "Sort Error in Refinement:" <+> pprint r 

-- DONT DELETE the below till we've added pred-checking as well
-- checkReft env emb (Just t) _ = checkSortedReft env xs (rTypeSortedReft emb t) 
--    where xs                  = fromMaybe [] $ params <$> stripRTypeBase t 

-- checkSig env (x, t) 
--   = case filter (not . (`S.member` env)) (freeSymbols t) of
--       [] -> True
--       ys -> errorstar (msg ys) 
--     where 
--       msg ys = printf "Unkown free symbols: %s in specification for %s \n%s\n" (showpp ys) (showpp x) (showpp t)


-------------------------------------------------------------------------------
------------------  Replace Predicate Arguments With Existentials -------------
-------------------------------------------------------------------------------

data ExSt = ExSt { fresh :: Int
                 , emap  :: M.HashMap Symbol (RSort, Expr)
                 , pmap  :: M.HashMap Symbol RPVar 
                 }

-- | Niki: please write more documentation for this, maybe an example? 
-- I can't really tell whats going on... (RJ)

txExpToBind   :: SpecType -> SpecType
txExpToBind t = evalState (expToBindT t) (ExSt 0 M.empty πs)
  where πs = M.fromList [(pname p, p) | p <- snd3 $ bkUniv t ]

expToBindT :: SpecType -> State ExSt SpecType
expToBindT (RVar v r) 
  = expToBindRef r >>= addExists . RVar v
expToBindT (RFun x t1 t2 r) 
  = do t1' <- expToBindT t1
       t2' <- expToBindT t2
       expToBindRef r >>= addExists . RFun x t1' t2'
expToBindT (RAllT a t) 
  = liftM (RAllT a) (expToBindT t)
expToBindT (RAllP p t)
  = liftM (RAllP p) (expToBindT t)
expToBindT (RApp c ts rs r) 
  = do ts' <- mapM expToBindT ts
       rs' <- mapM expToBindReft rs
       expToBindRef r >>= addExists . RApp c ts' rs'
expToBindT (RCls c ts)
  = liftM (RCls c) (mapM expToBindT ts)
expToBindT (RAppTy t1 t2 r)
  = do t1' <- expToBindT t1
       t2' <- expToBindT t2
       expToBindRef r >>= addExists . RAppTy t1' t2'
expToBindT t 
  = return t

expToBindReft :: Ref RSort RReft (SpecType) -> State ExSt (Ref RSort RReft SpecType)
expToBindReft (RPoly s t) = liftM (RPoly s) (expToBindT t)
expToBindReft (RMono s r) = liftM (RMono s) (expToBindRef r)

getBinds :: State ExSt (M.HashMap Symbol (RSort, Expr))
getBinds 
  = do bds <- emap <$> get
       modify $ \st -> st{emap = M.empty}
       return bds

addExists t = liftM (M.foldlWithKey' addExist t) getBinds

addExist t x (tx, e) = RAllE x t' t
  where t' = (ofRSort tx) `strengthen` uTop r
        r  = Reft (vv Nothing, [RConc (PAtom Eq (EVar (vv Nothing)) e)])

expToBindRef :: UReft r -> State ExSt (UReft r)
expToBindRef (U r (Pr p))
  = mapM expToBind p >>= return . U r . Pr

expToBind :: UsedPVar -> State ExSt UsedPVar
expToBind p
  = do Just π <- liftM (M.lookup (pname p)) (pmap <$> get)
       let pargs0 = zip (pargs p) (fst3 <$> pargs π)
       pargs' <- mapM expToBindParg pargs0
       return $ p{pargs = pargs'}

expToBindParg :: (((), Symbol, Expr), RSort) -> State ExSt ((), Symbol, Expr)
expToBindParg ((t, s, e), s') = liftM ((,,) t s) (expToBindExpr e s')

expToBindExpr :: Expr ->  RRType () -> State ExSt Expr
expToBindExpr e@(EVar (S (c:_))) _ | isLower c
  = return e
expToBindExpr e t         
  = do s <- freshSymbol
       modify $ \st -> st{emap = M.insert s (t, e) (emap st)}
       return $ EVar s

freshSymbol :: State ExSt Symbol
freshSymbol 
  = do n <- fresh <$> get
       modify $ \s -> s{fresh = n+1}
       return $ S $ "ex#" ++ show n


-------------------------------------------------------------------------------------
-- | Tasteful Error Messages --------------------------------------------------------
-------------------------------------------------------------------------------------

berrDataDecl  l c πs = printf "[%s]\nCannot convert data type %s with πs = %s" 
                         (showpp l) (showpp c) (showpp πs)
berrVarSpec   l v b  = printf "[%s]\nCannot convert\n    %s :: %s" 
                         (showpp l) (showpp v) (showpp b)
berrInvariant l i    = printf "[%s]\nCannot convert invariant\n    %s" 
                         (showpp l) (showpp i)
berrMeasure   l x t  = printf "[%s]\nCannot convert measure %s :: %s" 
                         (showpp l) (showpp x) (showpp t)

-- berrUnknownVar x     = printf "[%s]\nSpecification for unknown Variable : %s"  
--                          (showpp $ loc x) (showpp $ val x)
-- 
-- berrUnknownTyCon x   = printf "[%s]\nSpecification for unknown TyCon   : %s"  
--                          (showpp $ loc x) (showpp $ val x)
berrUnknownTyCon     = berrUnknown "TyCon"
berrUnknownVar       = berrUnknown "Variable"

berrUnknown :: (PPrint a) => String -> Located a -> String 
berrUnknown thing x  = printf "[%s]\nSpecification for unknown %s : %s"  
                         thing (showpp $ loc x) (showpp $ val x)






-- berrUnknownTyCon z   = printf "Specification for unknown variable: %s defined at: %s" 
--                          (showpp $ symbolString $ val z) (showpp $ loc z)
