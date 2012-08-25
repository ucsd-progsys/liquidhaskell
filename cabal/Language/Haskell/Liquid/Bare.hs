{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, ScopedTypeVariables  #-}

{- Raw description of pure types (without dependencies on GHC), suitable for
 - parsing from raw strings, and functions for converting between bare types
 - and real refinements. -}

module Language.Haskell.Liquid.Bare (GhcSpec (..), makeGhcSpec) where

import GHC hiding (lookupName)	
import Outputable
import Var
import PrelNames
import PrelInfo     (wiredInThings)
import Type         (eqType, expandTypeSynonyms, liftedTypeKind)

import HscTypes   (HscEnv)
import qualified CoreMonad as CM 
import GHC.Paths (libdir)

import System.Environment (getArgs)
import DynFlags (defaultDynFlags)
import HscMain
import TypeRep
import TysWiredIn
import DataCon  (dataConWorkId)
import BasicTypes (TupleSort (..), Boxity (..), Arity)
import TcRnDriver (tcRnLookupRdrName, tcRnLookupName) 

import TysPrim                  
import TysWiredIn               (listTyCon, intTy, intTyCon, boolTyCon, intDataCon, trueDataCon, falseDataCon)
import TyCon                    (tyConName, isAlgTyCon)
import DataCon                  (dataConName)
import Name                     (mkInternalName)

import OccName                  (mkTyVarOcc)
import Unique                   (getKey, getUnique, initTyVarUnique)
import Data.List                (sort, intercalate)
import Data.Maybe               (isJust, fromMaybe, catMaybes)
import Data.Char                (isUpper)
import ErrUtils
import Data.Traversable         (forM)
import Control.Applicative      ((<$>))
import Control.Monad.Reader     hiding (forM)
import Control.Monad.Error      hiding (forM)
import Data.Generics.Schemes
import Data.Generics.Aliases
import Data.Data                hiding (TyCon, tyConName)
import Data.Bifunctor

import qualified Data.Map as M

import Language.Haskell.Liquid.GhcMisc
import Language.Haskell.Liquid.Fixpoint
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.PredType
import qualified Language.Haskell.Liquid.Measure as Ms
import Language.Haskell.Liquid.Misc
import qualified Control.Exception as Ex

------------------------------------------------------------------
---------- Top Level Output --------------------------------------
------------------------------------------------------------------

data GhcSpec = SP {
    tySigs     :: ![(Var, SpecType)]     -- Asserted/Assumed Reftypes
                                         -- eg.  see include/Prelude.spec
  , ctor       :: ![(Var, RefType)]      -- Data Constructor Measure Sigs 
                                         -- eg.  (:) :: a -> xs:[a] -> {v: Int | v = 1 + len(xs) }
  , meas       :: ![(Symbol, RefType)]   -- Measure Types  
                                         -- eg.  len :: [a] -> Int
  , invariants :: ![SpecType]            -- Data Type Invariants
                                         -- eg.  forall a. {v: [a] | len(v) >= 0}
  , dconsP     :: ![(DataCon, DataConP)] -- Predicated Data-Constructors
                                         -- e.g. see tests/pos/Map.hs
  , tconsP     :: ![(TyCon, TyConP)]     -- Predicated Type-Constructors
                                         -- eg.  see tests/pos/Map.hs
  }

makeGhcSpec :: [Var] -> HscEnv -> Ms.Spec BareType Symbol -> IO GhcSpec 
makeGhcSpec vars env spec 
  = do (tcs, dcs) <- makeConTypes    env               $ Ms.dataDecls  spec 
       let tycons  = tcs ++ tcs'    
       let benv    = BE (makeTyConInfo tycons) env
       (cs, ms)   <- makeMeasureSpec benv $ Ms.mkMSpec $ Ms.measures   spec
       sigs       <- makeAssumeSpec  benv vars         $ Ms.sigs       spec
       invs       <- makeInvariants  benv              $ Ms.invariants spec 
       return      $ SP sigs cs ms invs (concat dcs ++ dcs') tycons  
    where (tcs', dcs') = wiredTyDataCons 

------------------------------------------------------------------
---------- Error-Reader-IO For Bare Transformation ---------------
------------------------------------------------------------------

type BareM a = ErrorT String (ReaderT BareEnv IO) a

data BareEnv = BE { tcEnv  :: !(M.Map TyCon RTyCon)
                  , hscEnv :: HscEnv }

execBare :: BareM a -> BareEnv -> IO a
execBare act benv = 
   do z <- runReaderT (runErrorT act) benv
      case z of
        Left s  -> errorstar $ "execBare:" ++ s
        Right x -> return x

wrapErr msg f x
  = f x `catchError` \e-> throwError $ "Bare Error " ++ "[" ++ msg ++ "]" ++ showPpr x ++ "(" ++ e ++ ")"

------------------------------------------------------------------
------------------- API: Bare Refinement Types -------------------
------------------------------------------------------------------

makeMeasureSpec :: BareEnv -> Ms.MSpec BareType Symbol -> IO ([(Var, RefType)], [(Symbol, RefType)])
makeMeasureSpec env m = execBare mkSpec env 
  where mkSpec = wrapErr "mkMeasureSort" mkMeasureSort m' >>= mkMeasureDCon >>= return . Ms.dataConTypes
        m'     = first (txTyVarBinds . mapReft ureft) m

makeAssumeSpec :: BareEnv -> [Var] -> [(Symbol, BareType)] -> IO [(Var, SpecType)]
makeAssumeSpec env vs xbs = execBare mkAspec env 
  where mkAspec = forM vbs mkVarSpec >>= return . checkAssumeSpec
        vbs     = joinIds vs (first symbolString <$> xbs) 

mkVarSpec (v, b) = liftM (v,) (wrapErr msg mkSpecType b)
  where msg = "mkVarSpec fails on " ++ showPpr v ++ " :: "  ++ showPpr b 

-- joinIds :: [Var] -> [(String, a)] -> [(Var, a)]
joinIds vs xts = {-tracePpr "spec vars"-} vts   
  where vm     = M.fromList [(showPpr v, v) | v <- {-tracePpr "vars"-} vs]
        vts    = catMaybes [(, t) <$> (M.lookup x vm) | (x, t) <- {-tracePpr "bareVars"-} xts]

makeInvariants :: BareEnv -> [BareType] -> IO [SpecType]
makeInvariants benv ts = execBare (mapM mkSpecType ts) benv

-- mkSpecType    :: BareType -> BareM SpecType 
mkSpecType 
  = ofBareType' 
  . txParams subvUReft [] 
  . txTyVarBinds 
  . mapReft (bimap canonReft stringTyVarTy) 

-- mkPredType :: [PVar Type]-> BRType (PVar String) (Predicate String) -> BareM PrType 
mkPredType πs 
  = ofBareType' 
  . txParams subvPredicate πs 
  . txTyVarBinds 
  . mapReft (fmap stringTyVarTy)

-----------------------------------------------------------------
------ Querying GHC for Id, Type, Class, Con etc. ---------------
-----------------------------------------------------------------

class GhcLookup a where
  lookupName :: HscEnv -> a -> IO (Maybe Name)
  candidates :: a -> [a]
  pp         :: a -> String 

instance GhcLookup String where
  lookupName     = stringLookup
  candidates x   = [x, swizzle x] 
  pp         x   = x

swizzle =  dropModuleNames . stripParens

instance GhcLookup Name where
  lookupName _   = return . Just
  candidates x   = [x]
  pp             = showPpr  

existsGhcThing :: (GhcLookup a) => String -> (TyThing -> Maybe b) -> a -> BareM Bool 
existsGhcThing name f x 
  = do z <- lookupGhcThing' name f x
       case z of 
         Just _ -> return True
         _      -> return False

lookupGhcThing :: (GhcLookup a) => String -> (TyThing -> Maybe b) -> a -> BareM b
lookupGhcThing name f x 
  = do zs <- catMaybes <$> mapM (lookupGhcThing' name f) (candidates x)
       case zs of 
         x:_ -> return x
         _   -> throwError $ "lookupGhcThing unknown " ++ name ++ " : " ++ (pp x)

lookupGhcThing' :: (GhcLookup a) => String -> (TyThing -> Maybe b) -> a -> BareM (Maybe b)
lookupGhcThing' name f x 
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
  = return Nothing -- errorstar $ "Unknown Primitive Thing: " ++ k
  | otherwise
  = stringLookupEnv env k

stringLookupEnv env s 
    = do L _ rn         <- hscParseIdentifier env s
         (_, lookupres) <- tcRnLookupRdrName env rn
         case lookupres of
           Just (n:_) -> return (Just n)
           _          -> return Nothing

lookupGhcTyCon = lookupGhcThing "TyCon" ftc 
  where ftc (ATyCon x) = Just x
        ftc _          = Nothing

lookupGhcClass = lookupGhcThing "Class" ftc 
  where ftc (ATyCon x) = tyConClass_maybe x 
        ftc _          = Nothing

lookupGhcDataCon = lookupGhcThing "DataCon" fdc 
  where fdc (ADataCon x) = Just x
        fdc _            = Nothing

lookupGhcId = lookupGhcThing "Id" thingId

-- existsGhcId = existsGhcThing "Id" thingId
existsGhcId s = 
  do z <- or <$> mapM (existsGhcThing "Id" thingId) (candidates s)
     if z 
       then return True 
       else return (warnShow ("existsGhcId " ++ s) $ False)


thingId (AnId x)     = Just x
thingId (ADataCon x) = Just $ dataConWorkId x
thingId _            = Nothing

wiredIn :: M.Map String Name
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
wiredTyDataCons = (\(x, y) -> (concat x, concat y)) $ unzip l
  where l = [listTyDataCons] ++ map tupleTyDataCons [1..maxArity] 

listTyDataCons :: ([(TyCon, TyConP)] , [(DataCon, DataConP)])
listTyDataCons = ( [(c, TyConP [(RTV tyv)] [p])]
                 , [(nilDataCon , DataConP [(RTV tyv)] [p] [] lt)
                 , (consDataCon, DataConP [(RTV tyv)] [p]  cargs  lt)])
    where c     = listTyCon
          [tyv] = tyConTyVars c
          t     = TyVarTy tyv
          fld   = stringSymbol "fld"
          x     = stringSymbol "x"
          xs    = stringSymbol "xs"
          p     = PV (stringSymbol "p") t [(t, fld, fld)]
          px    = pdVar $ PV (stringSymbol "p") t [(t, fld, x)]
          lt    = rApp c [xt] [RMono $ pdVar p] pdTrue 
          xt    = RVar (RV (RTV tyv)) pdTrue
          xst   = rApp c [RVar (RV (RTV tyv)) px] [RMono $ pdVar p] pdTrue
          cargs = [(xs, xst), (x, xt)]

tupleTyDataCons :: Int -> ([(TyCon, TyConP)] , [(DataCon, DataConP)])
tupleTyDataCons n = ( [(c, TyConP (RTV <$> tyv) ps)]
                    , [(dc, DataConP (RTV <$> tyv) ps  cargs  lt)])
  where c       = tupleTyCon BoxedTuple n
        dc      = tupleCon BoxedTuple n 
        tyv     = tyConTyVars c
        (ta:ts) = TyVarTy <$>tyv
        tvs     = tyv
        flds    = mks "fld"
        fld     = stringSymbol "fld"
        x1:xs   = mks "x"
        y       = stringSymbol "y"
        ps      = mkps pnames (ta:ts) ((fld,fld):(zip flds flds))
        pxs     = mkps pnames (ta:ts) ((fld, x1):(zip flds xs))
        lt      = rApp c ((\x -> RVar (RV (RTV x)) pdTrue) <$> tyv) 
                         (RMono . pdVar <$> ps) pdTrue 
        xts     = zipWith (\v p -> RVar (RV (RTV v))(pdVar p)) 
                          (tail tvs) pxs
        cargs   = reverse $ (x1, RVar (RV (RTV (head tvs))) pdTrue)
                            :(zip xs xts)
        pnames  = mks_ "p"
        mks  x  = (\i -> stringSymbol (x++ show i)) <$> [1..n]
        mks_ x  = (\i ->  (x++ show i)) <$> [2..n]


mkps ns (t:ts) ((f,x):fxs) = reverse $ mkps_ (stringSymbol <$> ns) ts fxs [(t, f, x)] [] 

mkps_ []     _       _          _    ps = ps
mkps_ (n:ns) (t:ts) ((f, x):xs) args ps
  = mkps_ ns ts xs (a:args) (p:ps)
  where p = PV n t args
        a = (t, f, x)

------------------------------------------------------------------------
----------------- Transforming Raw Strings using GHC Env ---------------
------------------------------------------------------------------------

ofBareType' = wrapErr "ofBareType" ofBareType

-- ofBareType :: (Reftable r) => BRType pv r -> BareM (RRType pv r)
-- ofBareType :: (TyConable a, Reftable r, GhcLookup a1, GhcLookup a) => RType a1 a String pv r-> BareM (RType Class RTyCon RTyVar pv r)
ofBareType (RVar (RV a) r) 
  = return $ RVar (stringRTyVar a) r
ofBareType (RVar (RP π) r) 
  = return $ RVar (RP π) r
ofBareType (RFun (RB x) t1 t2 _) 
  = liftM2 (rFun (RB x)) (ofBareType t1) (ofBareType t2)
ofBareType (RAll (RV a) t) 
  = liftM  (RAll (stringRTyVar a)) (ofBareType t)
ofBareType (RAll (RP π) t) 
  = liftM  (RAll (RP π)) (ofBareType t)
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

ofRef (RPoly t)   
  = liftM RPoly (ofBareType t)
ofRef (RMono r) 
  = return (RMono r)

-- TODO: move back to RefType
bareTCApp tyi r c rs ts 
  = if isTrivial t0 then t' else t
    where t0 = rAppOld tyi c ts rs top
          t  = rAppOld tyi c ts rs r
          t' = (expandRTypeSynonyms t0) `strengthen` r

rAppNew tyi c ts rs r = expandRApp tyi $ RApp (RTyCon c []) ts rs r
rAppOld _             = rApp

expandRTypeSynonyms = ofType . expandTypeSynonyms . toType

stringRTyVar  = rTyVar . stringTyVar 
stringTyVarTy = TyVarTy . stringTyVar



mkMeasureDCon :: (Data t) => Ms.MSpec t Symbol -> BareM (Ms.MSpec t DataCon)
mkMeasureDCon m = (forM (measureCtors m) $ \n -> liftM (n,) (lookupGhcDataCon n))
                  >>= (return . mkMeasureDCon_ m)

mkMeasureDCon_ :: Ms.MSpec t Symbol -> [(String, DataCon)] -> Ms.MSpec t DataCon
mkMeasureDCon_ m ndcs = m' {Ms.ctorMap = cm'}
  where m'  = fmap tx m
        cm' = M.mapKeys (dataConSymbol . tx) $ Ms.ctorMap m'
        tx  = mlookup (M.fromList ndcs) . symbolString

measureCtors ::  Ms.MSpec t Symbol -> [String]
measureCtors = nubSort . fmap (symbolString . Ms.ctor) . concat . M.elems . Ms.ctorMap 

-- mkMeasureSort :: (PVarable pv, Reftable r) => Ms.MSpec (BRType pv r) bndr-> BareM (Ms.MSpec (RRType pv r) bndr)
mkMeasureSort (Ms.MSpec cm mm) 
  = liftM (Ms.MSpec cm) $ forM mm $ \m -> 
      liftM (\s' -> m {Ms.sort = s'}) (ofBareType' (Ms.sort m))

-----------------------------------------------------------------------
---------------- Bare Predicate: DataCon Definitions ------------------
-----------------------------------------------------------------------

makeConTypes :: HscEnv -> [DataDecl] -> IO ([(TyCon, TyConP)], [[(DataCon, DataConP)]])
makeConTypes env dcs = unzip <$> execBare (mapM ofBDataDecl dcs) (BE M.empty env)

ofBDataDecl :: DataDecl -> BareM ((TyCon, TyConP), [(DataCon, DataConP)])
ofBDataDecl (D tc as ps cts)
  = do tc'   <- lookupGhcTyCon tc 
       cts'  <- mapM (ofBDataCon tc' αs πs) cpts
       return $ ((tc', TyConP αs πs), cts')
    where αs   = fmap (RTV . stringTyVar) as
          πs   = fmap (fmap stringTyVarTy) ps
          cpts = fmap (second (fmap (second (mapReft upred)))) cts

ofBDataCon tc αs πs (c, xts)
 = do c'  <- lookupGhcDataCon c
      ts' <- mapM (mkPredType πs) ts
      let t0 = rApp tc rs (RMono . pdVar <$> πs) pdTrue
      return $ (c', DataConP αs πs (reverse (zip xs' ts')) t0) 
 where (xs, ts) = unzip xts
       xs'      = map stringSymbol xs
       rs       = [RVar (RV α) pdTrue | α <- αs]

-----------------------------------------------------------------------
---------------- Bare Predicate: RefTypes -----------------------------
-----------------------------------------------------------------------

txTyVarBinds = mapBind fb
  where fb (RP π) = RP (stringTyVarTy <$> π)
        fb (RB x) = RB x
        fb (RV α) = RV α

-- txParams :: (Data p, Data c, Data tv, Data pv) =>[PVar Type]-> RType p c tv pv (UReft Reft Type)-> RType p c tv pv (UReft Reft Type)
-- txParams πs t = mapReft (second (mapPvar (txPvar (predMap πs t)))) t

--txParamsU πs t = mapReft (subvUReft     (txPvar (predMap πs t))) t
--txParamsP πs t = mapReft (subvPredicate (txPvar (predMap πs t))) t

txParams subv πs t = mapReft (subv (txPvar (predMap πs t))) t


txPvar m π = π { pargs = args' }
  where args' = zipWith (\(t,x,_) (_,_,y) -> (t, x, y)) (pargs π') (pargs π)
        π'    = M.findWithDefault (errorstar err) (pname π) m
        err   = "Bare.replaceParams Unbound Predicate Variable: " ++ show π

predMap πs t = Ex.assert (M.size xπm == length xπs) xπm 
  where xπm = M.fromList xπs
        xπs = [(pname π, π) | π <- πs ++ rtypePredBinds t]

rtypePredBinds t = everything (++) ([] `mkQ` grab) t
  where grab ((RAll (RP pv) _) :: BRType (PVar Type) (Predicate Type)) = [pv]
        grab _                = []

-------------------------------------------------------------------------------
------- Checking Specifications Refine Haskell Types --------------------------
-------------------------------------------------------------------------------

checkAssumeSpec xts 
  = case filter specMismatch xts of 
      []  -> xts
      yts -> errorstar $ specificationError yts

specificationError yts = unlines $ "Error in Reftype Specification" : concatMap err yts 
  where err (y, t) = [ "Haskell: " ++ showPpr y ++ " :: " ++ showPpr (varType y)
                     , "Liquid : " ++ showPpr y ++ " :: " ++ showPpr t           ]
  
specMismatch (x, t) 
  =  not $ eqShape t (ofType $ varType x) 

---------------------------------------------------------------------------------
----------------- Helper Predicates on Types ------------------------------------
---------------------------------------------------------------------------------

eqType' τ1 τ2 
  = eqType τ1 τ2 

eqShape :: SpecType -> SpecType -> Bool 
eqShape t1 t2 
  = eqShape' t1 t2 

eqShape' (RAll (RP _) t) (RAll (RP _) t') 
  = eqShape t t'
eqShape' (RAll (RP _) t) t' 
  = eqShape t t'
eqShape' (RAll (RV a@(RTV α)) t) (RAll (RV a') t')
  = eqShape t (subsTyVar_meet (a', TyVarTy α, RVar (RV a) top) t')
    -- GENSUB: eqShape t (subsTyVar_meet (a', RVar (RV a) top) t')
eqShape' (RFun _ t1 t2 _) (RFun _ t1' t2' _) 
  = eqShape t1 t1' && eqShape t2 t2'
eqShape' t@(RApp c ts _ _) t'@(RApp c' ts' _ _)
  =  ((c == c') && length ts == length ts' && and (zipWith eqShape ts ts'))
eqShape' (RCls c ts) (RCls c' ts')
  = (c == c') && length ts == length ts' && and (zipWith eqShape ts ts')
eqShape' (RVar (RV α) _) (RVar (RV α') _)
  = α == α' 
eqShape' t1 t2 
  = False



