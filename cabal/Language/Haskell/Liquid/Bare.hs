{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, ScopedTypeVariables  #-}

{- Raw description of pure types (without dependencies on GHC), suitable for
 - parsing from raw strings, and functions for converting between bare types
 - and real refinements. -}

module Language.Haskell.Liquid.Bare (
    DataDecl (..)
  , mkMeasureSpec
  , mkAssumeSpec
  , mkConTypes
  -- , mkIds, mkRefTypes, mkPredTypes
  -- , getClasses
  -- , isDummyBind
  )
where

import GHC hiding (lookupName)	
import Outputable
import Var
import PrelNames

import Type       (liftedTypeKind)
import HscTypes   (HscEnv)
import qualified CoreMonad as CM 
import GHC.Paths (libdir)

import System.Environment (getArgs)
import DynFlags (defaultDynFlags)
import HscMain
import TypeRep
import TysWiredIn
import DataCon  (dataConWorkId)
import BasicTypes (TupleSort (..), Boxity (..))
import TcRnDriver (tcRnLookupRdrName, tcRnLookupName) 

import TysPrim                  (intPrimTyCon)
import TysWiredIn               (listTyCon, intTy, intTyCon, boolTyCon, intDataCon, trueDataCon, falseDataCon)
import TyCon                    (tyConName, isAlgTyCon)
import DataCon                  (dataConName)
import Name                     (mkInternalName)

import OccName                  (mkTyVarOcc)
import Unique                   (getKey, getUnique, initTyVarUnique)
import Data.List                (sort)
import Data.Char                (isUpper)
import ErrUtils
import Data.Traversable         (forM)
import Control.Applicative      ((<$>))
import Control.Monad.Reader     hiding (forM)
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
------------------- API: Bare Refinement Types -------------------
------------------------------------------------------------------

--mkRefTypes :: HscEnv -> [BRType a Reft] -> IO [RRType a Reft]
--mkRefTypes env bs = runReaderT (mapM mkRefType bs) env
 --mkIds :: HscEnv -> [Name] -> IO [Var]
--mkIds env ns = runReaderT (mapM lookupGhcId ns) env


mkMeasureSpec :: HscEnv -> Ms.MSpec BareType Symbol -> IO ([(Var, RefType)], [(Symbol, RefType)])
-- mkMeasureSpec :: HscEnv -> Ms.MSpec (BRType (PVar Type) Reft) Symbol -> IO ([(Var, RefType)], [(Symbol, RefType)])
mkMeasureSpec env m = runReaderT mkSpec env
  where mkSpec = mkMeasureSort m' >>= mkMeasureDCon >>= return . Ms.dataConTypes
        m'     = first (txTyVarBinds . mapReft ureft) m

mkAssumeSpec :: HscEnv-> [(Symbol, BareType)] -> IO [(Var, SpecType)]
mkAssumeSpec env xbs = runReaderT mkAspec env
  where mkAspec = forM xbs $ \(x, b) -> liftM2 (,) (lookupGhcId $ symbolString x) (mkSpecType b)

-- mkSpecType :: BareType -> BareM SpecType 
mkSpecType    = ofBareType . txParams [] . txTyVarBinds . mapReft (bimap canonReft stringTyVarTy) 
mkPredType πs = ofBareType . txParams πs . txTyVarBinds . mapReft (fmap stringTyVarTy)
-- mkRefType     = ofBareType . mapReft canonReft

------------------------------------------------------------------
-------------------- Type Checking Raw Strings -------------------
------------------------------------------------------------------

tcExpr ::  FilePath -> String -> IO Type
tcExpr f s = 
    runGhc (Just libdir) $ do
      df   <- getSessionDynFlags
      setSessionDynFlags df
      cm0  <- compileToCoreModule f
      setContext [IIModule (cm_module cm0)]
      env  <- getSession
      r    <- CM.liftIO $ hscTcExpr env s 
      return r

fileEnv f 
  = runGhc (Just libdir) $ do
      df    <- getSessionDynFlags
      setSessionDynFlags df
      cm0  <- compileToCoreModule f
      setContext [IIModule (cm_module cm0)]
      env   <- getSession
      return env

-----------------------------------------------------------------
------ Querying GHC for Id, Type, Class, Con etc. ---------------
-----------------------------------------------------------------

class Outputable a => GhcLookup a where
  lookupName :: HscEnv -> a -> IO Name

instance GhcLookup String where
  lookupName = stringToName

instance GhcLookup Name where
  lookupName _  = return

lookupGhcThing :: (GhcLookup a) => String -> (TyThing -> Maybe b) -> a -> BareM b
lookupGhcThing name f x 
  = do env     <- ask
       (_,res) <- liftIO $ tcRnLookupName env =<< lookupName env x
       case f `fmap` res of
         Just (Just z) -> 
           return z
         _      -> 
           liftIO $ ioError $ userError $ "lookupGhcThing unknown " ++ name ++ " : " ++ (showPpr x)

lookupGhcThingToSymbol :: (TyThing -> Maybe Symbol) -> String -> BareM Symbol
lookupGhcThingToSymbol f x 
  = do env     <- ask
       m <- liftIO $ lookupNameStr env x 
       case m of 
          Just n -> do  (_,res) <- liftIO $ tcRnLookupName env n
                        case f `fmap` res of
                          Just (Just z) -> return z
                          _      -> return $ S x
          _      -> return $ S x

lookupNameStr :: HscEnv -> String -> IO (Maybe Name)
lookupNameStr env k 
  = case M.lookup k wiredIn of 
      Just n  -> return (Just n)
      Nothing -> stringToNameEnvStr env k

stringToNameEnvStr :: HscEnv -> String -> IO ( Maybe Name)
stringToNameEnvStr env s 
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

lookupGhcId s 
  = lookupGhcThing "Id" fid s
  where fid (AnId x)     = Just x
        fid (ADataCon x) = Just $ dataConWorkId x
        fid _            = Nothing

stringToName :: HscEnv -> String -> IO Name
stringToName env k 
  = case M.lookup k wiredIn of 
      Just n  -> return n
      Nothing -> stringToNameEnv env k

stringToNameEnv :: HscEnv -> String -> IO Name
stringToNameEnv env s 
    = do L _ rn         <- hscParseIdentifier env s
         (_, lookupres) <- tcRnLookupRdrName env rn
         case lookupres of
           Just (n:_) -> return n
           _          -> errorstar $ "Bare.lookupName cannot find name for: " ++ s

symbolToSymbol :: Symbol -> BareM Symbol
symbolToSymbol (S s) 
  = lookupGhcThingToSymbol fid s
  where fid (AnId x)     = Just $ mkSymbol x
        fid (ADataCon x) = Just $ mkSymbol $ dataConWorkId x
        fid _            = Nothing

wiredIn :: M.Map String Name
wiredIn = M.fromList $
  [ ("GHC.Integer.smallInteger" , smallIntegerName) 
  , ("GHC.Num.fromInteger"      , fromIntegerName)
  , ("GHC.Types.I#"             , dataConName intDataCon)
  , ("GHC.Prim.Int#"            , tyConName intPrimTyCon) 
  ]

------------------------------------------------------------------------
----------------- Transforming Raw Strings using GHC Env ---------------
------------------------------------------------------------------------

type BareM a = ReaderT HscEnv IO a

ofBareType :: BRType pv r -> BareM (RRType pv r)
ofBareType (RVar (RV a) r) 
  = return $ RVar (stringRTyVar a) r
ofBareType (RVar (RP π) r) 
  = return $ RVar (RP π) r
ofBareType (RFun (RB x) t1 t2) 
  = liftM2 (RFun (RB x)) (ofBareType t1) (ofBareType t2)
ofBareType (RAll (RV a) t) 
  = liftM  (RAll (stringRTyVar a)) (ofBareType t)
ofBareType (RAll (RP π) t) 
  = liftM  (RAll (RP π)) (ofBareType t)
ofBareType (RApp tc [t] [] r) 
  = liftM (bareTCApp r [] listTyCon . (:[])) (ofBareType t)
ofBareType (RApp tc ts [] r) 
  | isTuple tc
  = liftM (bareTCApp r [] c) (mapM ofBareType ts)
    where c = tupleTyCon BoxedTuple (length ts)
ofBareType (RApp tc ts rs r) 
  = liftM2 (bareTCApp r rs) (lookupGhcTyCon tc) (mapM ofBareType ts)
ofBareType (RCls c ts)
  = liftM2 RCls (lookupGhcClass c) (mapM ofBareType ts)

-- TODO: move back to RefType
bareTCApp r rs c ts 
  = rApp c ts rs r -- RApp (RTyCon c []) ts rs r

rbind ""    = RB dummySymbol
rbind s     = RB $ stringSymbol s


stringRTyVar  = rTyVar . stringTyVar 
stringTyVarTy = TyVarTy . stringTyVar

isDummyBind (RB s) = s == dummySymbol 


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

mkMeasureSort :: Ms.MSpec (BRType pv r) bndr-> BareM (Ms.MSpec (RRType pv r) bndr)
mkMeasureSort (Ms.MSpec cm mm) 
  = liftM (Ms.MSpec cm) $ forM mm $ \m -> 
      liftM (\s' -> m {Ms.sort = s'}) (ofBareType (Ms.sort m))

-----------------------------------------------------------------------
---------------- Bare Predicate: DataCon Definitions ------------------
-----------------------------------------------------------------------

mkConTypes :: HscEnv-> [DataDecl] -> IO ([(TyCon, TyConP)], [[(DataCon, DataConP)]])
mkConTypes env dcs = unzip <$> runReaderT (mapM ofBDataDecl dcs) env

ofBDataDecl :: DataDecl-> BareM ((TyCon, TyConP), [(DataCon, DataConP)])
ofBDataDecl (D tc as ps cts)
  = do tc'   <- lookupGhcTyCon tc 
       cts'  <- mapM (ofBDataCon tc' αs πs) cts
       return $ ((tc', TyConP αs πs), cts')
    where αs = fmap stringTyVar as
          πs = fmap (fmap stringTyVarTy) ps

ofBDataCon tc αs πs (c, xts)
 = do c'  <- lookupGhcDataCon c
      ts' <- mapM (mkPredType πs) ts
      let t0 = rApp tc (flip rVar pdTrue <$> αs) (pdVar <$> πs) pdTrue
      -- let t2 = foldl (\t' (x,t) -> RFun (RB x) t t') t0 (zip xs' ts')
      -- let t1 = foldl (\t pv -> RAll (RP pv) t) t2 πs 
      -- let t  = foldl (\t v -> RAll (RV v) t) t1 αs
      return $ (c', DataConP αs πs (reverse (zip xs' ts')) t0) 
 where (xs, ts) = unzip xts
       xs'      = map stringSymbol xs

-----------------------------------------------------------------------
---------------- Bare Predicate: RefTypes -----------------------------
-----------------------------------------------------------------------

--mkPredTypes :: HscEnv -> [(Symbol, BRType (PVar String) (Predicate String))]-> IO [(Id, RRType (PVar Type) (Predicate Type))]
--mkPredTypes env xbs = runReaderT (mapM mkBind xbs) env
--  where mkBind (x, b) = liftM2 (,) (lookupGhcId $ symbolString x) (mkPredType [] b)
-- mkPredType πs = ofBareType . txParams πs . txTyVars
-- txTyVars = txTyVarBinds . mapReft (second stringTyVarTy) 

txTyVarBinds = mapBind fb
  where fb (RP π) = RP (stringTyVarTy <$> π)
        fb (RB x) = RB x
        fb (RV α) = RV α

txParams πs t = mapReft (subv (txPvar (predMap πs t))) t

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

