{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, ScopedTypeVariables  #-}

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
import Id                       (isConLikeId)
import PrelNames
import PrelInfo                 (wiredInThings)
import Type                     (expandTypeSynonyms, splitFunTy_maybe)
import DataCon                  (dataConImplicitIds)
import TyCon                    (tyConArity)
import HscMain
import TysWiredIn
import BasicTypes               (TupleSort (..), Arity)
import TcRnDriver               (tcRnLookupRdrName, tcRnLookupName) 
import Data.Char                (isLower)
import Text.Printf
import Data.Maybe               (listToMaybe, fromMaybe, mapMaybe, catMaybes, isNothing)
import Control.Monad.State      (put, get, modify, State, evalState, execState)
import Data.Traversable         (forM)
import Control.Applicative      ((<$>), (<|>))
import Control.Monad.Reader     hiding (forM)
import Control.Monad.Error      hiding (Error, forM)
import Control.Monad.Writer     hiding (forM)
import qualified Control.Exception as Ex 
-- import Data.Data                hiding (TyCon, tyConName)
import Data.Bifunctor


import Language.Fixpoint.Names                  (propConName, takeModuleNames, dropModuleNames)
import Language.Haskell.Liquid.GhcMisc          hiding (L)
import Language.Fixpoint.Types                  
import Language.Fixpoint.Sort                   (checkSortedReftFull)
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.PredType
import qualified Language.Haskell.Liquid.Measure as Ms
import Language.Fixpoint.Misc

import qualified Data.List           as L
import qualified Data.HashSet        as S
import qualified Data.HashMap.Strict as M
import TypeRep
------------------------------------------------------------------
---------- Top Level Output --------------------------------------
------------------------------------------------------------------

makeGhcSpec, makeGhcSpec' :: Config -> String -> [Var] -> [Var] -> HscEnv -> Ms.Spec BareType Symbol -> IO GhcSpec 
makeGhcSpec cfg name vars defVars env spec 
  = either Ex.throw return . checkGhcSpec =<< makeGhcSpec' cfg name vars defVars env spec 

makeGhcSpec' cfg name vars defVars env spec 
  = do (tcs, dcs)      <- makeConTypes    env  name         $ Ms.dataDecls  spec 
       let (tcs', dcs') = wiredTyDataCons 
       let tycons       = tcs ++ tcs'    
       let datacons     = concat dcs ++ dcs'    
       let benv         = BE name (makeTyConInfo tycons) env
       (cs, ms)        <- makeMeasureSpec benv $ Ms.mkMSpec $ Ms.measures   spec
       sigs'           <- makeAssumeSpec  cfg benv vars     $ Ms.sigs       spec
       invs            <- makeInvariants  benv              $ Ms.invariants spec
       embs            <- makeTyConEmbeds benv              $ Ms.embeds     spec
       targetVars      <- makeTargetVars  env name defVars  $ binders cfg
       let lazies       = makeLazies      vars              $ Ms.lazy       spec
       let sigs         = [(x, (txRefSort embs benv . txExpToBind) <$> t) | (x, t) <- sigs'] 
       let cs'          = mapSnd (Loc dummyPos) <$> meetDataConSpec cs datacons
       let ms'          = [ (x, Loc l t) | (Loc l x, t) <- ms ] -- first val <$> ms 
       let syms         = makeSymbols (vars ++ map fst cs') (map fst ms) (sigs ++ cs') ms' 
       let tx           = subsFreeSymbols syms
       let syms'        = [(varSymbol v, v) | (_, v) <- syms]
       let decr'        = makeHints defVars (Ms.decr spec)
       return           $ SP { tySigs     = renameTyVars <$> tx sigs
                             , ctor       = tx cs'
                             , meas       = tx (ms' ++ varMeasures vars) 
                             , invariants = invs 
                             , dconsP     = datacons
                             , tconsP     = tycons 
                             , freeSyms   = syms' 
                             , tcEmbeds   = embs 
                             , qualifiers = Ms.qualifiers spec 
                             , decr       = decr'
                             , lazy       = lazies
                             , tgtVars    = targetVars
                             }
       
-- goo sp = either id (\z -> sp {tySigs = z}) $ mapM renameTyVars $ tySigs sp

makeHints :: [Var] -> [(LocSymbol, [Int])] -> [(Var, [Int])]
makeHints vs       = concatMap go
  where lvs        = M.map L.sort $ group [(varSymbol v, locVar v) | v <- vs]
        varSymbol  = stringSymbol . dropModuleNames . showPpr
        locVar v   = (getSourcePos v, v)
        go (s, ns) = case M.lookup (val s) lvs of 
                     Just lvs -> (, ns) <$> varsAfter s lvs
                     Nothing  -> errorstar $ msg s
        msg s      = printf "%s: Hint for Undefined Var %s" 
                         (show (loc s)) (show (val s))
       
varsAfter s lvs 
  | eqList (fst <$> lvs)
  = snd <$> lvs
  | otherwise
  = map snd $ takeEqLoc $ dropLeLoc lvs
  where takeEqLoc xs@((l, _):_) = L.takeWhile ((l==) . fst) xs
        takeEqLoc []            = []
        dropLeLoc               = L.dropWhile ((loc s >) . fst)
        eqList []               = True
        eqList (x:xs)           = all (==x) xs

txRefSort embs benv = mapBot (addSymSort embs (tcEnv benv))

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

varMeasures vars  = [ (varSymbol v, varSpecType v) 
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
  = EVar $ varSymbol v
  where t            = varType v
        (tvs, tbase) = splitForAllTys t
        tfun         = splitFunTy_maybe tbase

-- subsFreeSymbols     :: [(Symbol, Var)] -> f (t1, t2) -> f (t1, t2)
subsFreeSymbols xvs = tx
  where 
    su              = mkSubst [ (x, mkVarExpr v) | (x, v) <- xvs]
    tx              = fmap $ mapSnd $ subst su 

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

type BareM a = WriterT [Warn] (ErrorT String (ReaderT BareEnv IO)) a

type Warn    = String

data BareEnv = BE { modName :: !String 
                  , tcEnv   :: !(M.HashMap TyCon RTyCon)
                  , hscEnv  :: HscEnv }

execBare :: BareM a -> BareEnv -> IO a
execBare act benv = 
   do z <- runReaderT (runErrorT (runWriterT act)) benv
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

makeMeasureSpec :: BareEnv 
                -> Ms.MSpec BareType Symbol 
                -> IO ([(Var, SpecType)], [(LocSymbol, RefType)])

makeMeasureSpec env m = execBare mkSpec env 
  where 
    mkSpec            = wrapErr "mkMeasureSort" mkMeasureSort m' 
                          >>= mkMeasureDCon 
                          >>= return . mapFst (mapSnd uRType <$>) . Ms.dataConTypes 
    m'                = first (mapReft ur_reft) m


makeTargetVars :: HscEnv -> String -> [Var] -> [String] -> IO [Var]
makeTargetVars env name vs ss = do
  ns <- catMaybes <$> mapM (lookupName env) (map prefix ss)
  return $ filter ((`elem` ns) . varName) vs
 where
  prefix s = name ++ "." ++ s


makeAssumeSpec :: Config -> BareEnv -> [Var] -> [(LocSymbol, BareType)] -> IO [(Var, Located SpecType)]
makeAssumeSpec cfg env vs xbs = execBare mkAspec env
  where 
    vbs                       = joinIds vs xbs 
    mkAspec                   = do when (not $ noCheckUnknown cfg)
                                     $ checkDefAsserts env vbs xbs
                                   forM vbs mkVarSpec

checkDefAsserts :: BareEnv -> [(Var, LocSymbol, BareType)] -> [(LocSymbol, BareType)] -> BareM ()
checkDefAsserts env vbs xbs   = applyNonNull (return ()) grumble  undefSigs
  where
    undefSigs                 = [x | (x, _) <- assertSigs, not (x `S.member` definedSigs)]
    assertSigs                = filter isTarget xbs
    definedSigs               = S.fromList $ snd3 <$> vbs
    grumble xs                = mapM_ (warn . berrUnknownVar) xs -- [berrUnknownVar (loc x) (val x) | x <- xs] 
    moduleName                = modName env
    isTarget                  = L.isPrefixOf moduleName . symbolStringRaw . val . fst
    symbolStringRaw           = stripParens . symbolString

    -- grumble                   = {- throwError -} warn . render . vcat . fmap errorMsg
    -- errorMsg                  = (text "Specification for unknown variable:" <+>) . locatedSymbolText
 

warn x = tell [x]





mkVarSpec                 :: (Var, LocSymbol, BareType) -> BareM (Var, Located SpecType)
mkVarSpec (v, Loc l _, b) = ((v, ) . (Loc l)) <$> mkSpecType msg b
  where 
    msg                   = berrVarSpec l v b



showTopLevelVars vs = 
  forM vs $ \v -> 
    if isExportedId v 
      then donePhase Loud ("Exported: " ++ showPpr v)
      else return ()

----------------------------------------------------------------------

makeTyConEmbeds  :: BareEnv -> TCEmb (Located String) -> IO (TCEmb TyCon) 
makeTyConEmbeds benv z = execBare (M.fromList <$> mapM tx (M.toList z)) benv
  where 
    tx (c, y) = (, y) <$> lookupGhcTyCon' c --  wrapErr () (lookupGhcTyCon (val c))
     

lookupGhcTyCon' c = wrapErr msg lookupGhcTyCon (val c)
  where 
    msg :: String = berrUnknownTyCon c


makeLazies :: [Var] -> S.HashSet Symbol -> S.HashSet Var
makeLazies vs s = S.fromList $ fst3 <$> joinIds vs xxs
  where xs  = S.toList s
        xxs = zip xs xs

makeInvariants :: BareEnv -> [Located BareType] -> IO [Located SpecType]
makeInvariants benv ts = execBare (mapM mkI ts) benv
  where 
    mkI (Loc l t)      = liftM (Loc l) $ mkSpecType (berrInvariant l t) t 

mkSpecType msg t = mkSpecType' msg (snd3 $ bkUniv t)  t

mkSpecType' :: String -> [PVar BSort] -> BareType -> BareM SpecType
mkSpecType' msg πs = ofBareType' msg . txParams subvUReft (uPVar <$> πs)

makeSymbols :: (PPrint r1, PPrint r, Reftable r1, Reftable r) 
            => [Var] 
            -> [LocSymbol] 
            -> [(a, Located (RType p c tv r))] 
            -> [(a1, Located (RType p1 c1 tv1 r1))] 
            -> [(Symbol, Var)]
makeSymbols vs xs' xts yts = xvs 
  where
    xs'' = val <$> xs' 
    zs   = (concatMap freeSymbols ((snd <$> xts))) `sortDiff` xs''
    zs'  = (concatMap freeSymbols ((snd <$> yts))) `sortDiff` xs''
    xs   = sortNub $ zs ++ zs'
    xvs  = sortNub [(x, v) | (v, _, x) <- joinIds vs (zip xs xs)]

joinIds        ::  (Symbolic a) => [Var] -> [(a, t)] -> [(Var, a, t)]
joinIds vs xts = catMaybes [(, x, t) <$> tx x | (x, t) <- xts]   
  where 
    vm         = group [(showpp v, v) | v <- vs]
    tx x       = listToMaybe $ filter (symCompat x) $ M.lookupDefault [] (ss x) vm
    ss         = symbolString . symbol

symCompat :: (Symbolic a) => a -> Var -> Bool
symCompat x v   = (symbolString $ symbol x) `comp` (showpp v)
  where 
    comp sx sv  = sx == sv || (takeModuleNames sx `L.isPrefixOf` takeModuleNames sv)


freeSymbols ty = sortNub $ concat $ efoldReft (\_ _ -> []) (\ _ -> ()) f emptySEnv [] (val ty)
  where 
    f γ _ r xs = let Reft (v, _) = toReft r in 
                 [ x | x <- syms r, x /= v, not (x `memberSEnv` γ)] : xs

-----------------------------------------------------------------
------ Querying GHC for Id, Type, Class, Con etc. ---------------
-----------------------------------------------------------------

class GhcLookup a where
  lookupName :: HscEnv -> a -> IO (Maybe Name)
  candidates :: a -> [a]
  pp         :: a -> String 

instance GhcLookup String where
  lookupName     = stringLookup
  candidates x   = [x, dropModuleNames x] 
  pp         x   = x

instance GhcLookup Name where
  lookupName _   = return . Just
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
  = do env     <- hscEnv <$> ask
       z       <- liftIO $ lookupName env x
       case z of
         Nothing -> return Nothing 
         Just n  -> liftIO $ liftM (join . (f <$>) . snd) (tcRnLookupName env n)

stringLookup :: HscEnv -> String -> IO (Maybe Name)
stringLookup env k
  | k `M.member` wiredIn
  = return $ M.lookup k wiredIn
  | last k == '#'
  = return Nothing
  | otherwise
  = stringLookupEnv env k

stringLookupEnv env s 
    = do L _ rn         <- hscParseIdentifier env s
         (_, lookupres) <- tcRnLookupRdrName env rn
         case lookupres of
           Just (n:_) -> return (Just n)
           _          -> return Nothing

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
                   , [(nilDataCon , DataConP [(RTV tyv)] [p] [] lt)
                   , (consDataCon, DataConP [(RTV tyv)] [p]  cargs  lt)])
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
                    , [(dc, DataConP (RTV <$> tyvs) ps  cargs  lt)])
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
ofBareType (RAppTy t1 t2 _) 
  = liftM2 rAppTy (ofBareType t1) (ofBareType t2)
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
  = do tyi <- tcEnv <$> ask
       liftM2 (bareTCApp tyi r listTyCon) (mapM ofRef rs) (mapM ofBareType ts)
ofBareType (RApp tc ts rs r) 
  | isTuple tc
  = do tyi <- tcEnv <$> ask
       liftM2 (bareTCApp tyi r c) (mapM ofRef rs) (mapM ofBareType ts)
    where c = tupleTyCon BoxedTuple (length ts)
ofBareType (RApp tc ts rs r) 
  = do tyi <- tcEnv <$> ask
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
measureCtors = sortNub . fmap (symbolString . Ms.ctor) . concat . M.elems . Ms.ctorMap 

-- mkMeasureSort :: (PVarable pv, Reftable r) => Ms.MSpec (BRType pv r) bndr-> BareM (Ms.MSpec (RRType pv r) bndr)
mkMeasureSort (Ms.MSpec cm mm) 
  = liftM (Ms.MSpec cm) $ forM mm $ \m -> 
      liftM (\s' -> m {Ms.sort = s'}) (ofBareType' (msg m) (Ms.sort m))
    where 
      msg m = berrMeasure (loc $ Ms.name m) (Ms.name m) (Ms.sort m) 



-----------------------------------------------------------------------
----------------------- Prop TyCon Definition -------------------------
-----------------------------------------------------------------------

propTyCon   = stringTyCon 'w' 24 propConName
-- propMeasure = (stringSymbolRaw propConName, FFunc  

-----------------------------------------------------------------------
---------------- Bare Predicate: DataCon Definitions ------------------
-----------------------------------------------------------------------

makeConTypes :: HscEnv -> String -> [DataDecl] -> IO ([(TyCon, TyConP)], [[(DataCon, DataConP)]])
makeConTypes env name dcs = unzip <$> execBare (mapM ofBDataDecl dcs) (BE name M.empty env)

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
       let t0   = rApp tc rs (RMono [] . pdVarReft <$> πs) top 
       return   $ (c', DataConP αs πs (reverse (zip xs' ts')) t0) 
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

checkGhcSpec :: GhcSpec -> Either [Error] GhcSpec 
checkGhcSpec = errorstar "TOBD: HEREHEREHEREHEREHERE"

-- OLD -- checkGhcSpec sp      =  applyNonNull sp specError errors
-- OLD --   where 
-- OLD --     env              =  ghcSpecEnv sp
-- OLD --     emb              =  tcEmbeds sp
-- OLD --     errors           =  mapMaybe (checkBind "variable"         emb env) (tySigs     sp)
-- OLD --                      ++ mapMaybe (checkBind "data constructor" emb env) (dcons      sp)
-- OLD --                      ++ mapMaybe (checkBind "measure"          emb env) (meas       sp)
-- OLD --                      ++ mapMaybe (checkInv  emb env)                    (invariants sp)
-- OLD --                      ++ mapMaybe checkMismatch                          (tySigs     sp)
-- OLD --                      ++ checkDuplicate                                  (tySigs     sp)
-- OLD --     dcons spec       = mapSnd (Loc dummyPos) <$> dataConSpec (dconsP spec) 


specError            = errorstar 
                     . render 
                     . vcat 
                     . punctuate (text "\n----\n") 
                     . (text "Alas, errors found in specification..." :)

checkInv :: TCEmb TyCon -> SEnv SortedReft -> Located (RRType r) -> Maybe Error
checkInv emb env t   = checkTy err emb env (val t) 
  where 
    err              = BadInvt (sourcePosSrcSpan $ loc t) (val t)


checkBind :: String -> TCEmb TyCon -> SEnv SortedReft -> (t, Located (RRType r)) -> Maybe Error 
checkBind d emb env (v, Loc l t) = checkTy msg emb env t
  where 
    msg = text "Error in type specification for" <+> text d 
          $+$ text "defined at: " <+> pprint l
          $+$ pprint v <+> dcolon  <+> pprint t


checkTy :: (Doc -> Error) -> TCEmb TyCon -> SEnv SortedReft -> RRType r -> Maybe Error
checkTy mkE emb env t    = mkE <$> checkRType emb env t

checkDuplicate :: [(a,a)] -> [Error]
checkDuplicate xts   = err <$> dups
  where err (x,ts)   = vcat $ (text "Multiple Specifications for" <+> pprint x) : (pprint <$> ts)
        dups         = [ z | z@(x, t1:t2:_) <- M.toList $ group xts ]

checkMismatch        :: (Var, Located (RRType r)) -> Maybe Error
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
    binds            =  [(x,           rSort t) | (x, Loc _ t) <- meas sp] 
                     ++ [(varSymbol v, rSort t) | (v, Loc _ t) <- ctor sp] 
                     ++ [(x          , vSort v) | (x, v) <- freeSyms sp, isConLikeId v] 
    rSort            = rTypeSortedReft emb 
    vSort            = rSort . varRType 
    varRType         :: Var -> RRType ()
    varRType         = ofType . varType

errTypeMismatch     :: Var -> Located (RRType r) -> Error
errTypeMismatch x t = vcat [ text "Specified Liquid Type Does Not Match Haskell Type"
                           , text "Haskell:" <+> pprint x <+> dcolon <+> pprint (varType x)
                           , text "Liquid :" <+> pprint x <+> dcolon <+> pprint t           
                           ]

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
