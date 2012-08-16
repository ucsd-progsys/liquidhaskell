{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, ScopedTypeVariables  #-}

{- Raw description of pure types (without dependencies on GHC), suitable for
 - parsing from raw strings, and functions for converting between bare types
 - and real refinements. -}

module Language.Haskell.Liquid.Bare (
    makeMeasureSpec
  , makeAssumeSpec
  , makeInvariants
  , makeConTypes
  , checkAssertSpec
  , makeRTAliasEnv
  )
where

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
import BasicTypes (TupleSort (..), Boxity (..))
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
---------- Error-Reader-IO For Bare Transformation ---------------
------------------------------------------------------------------

type BareM a = ErrorT String (ReaderT HscEnv IO) a

execBare :: BareM a -> HscEnv -> IO a
execBare act hsc_env = 
   do z <- runReaderT (runErrorT act) hsc_env
      case z of
        Left s  -> errorstar $ "execBare:" ++ s
        Right x -> return x

wrapErr msg f x
  = f x `catchError` \e-> throwError $ "Bare Error " ++ "[" ++ msg ++ "]" ++ showPpr x ++ "(" ++ e ++ ")"

------------------------------------------------------------------
------------------- API: Bare Refinement Types -------------------
------------------------------------------------------------------

makeMeasureSpec :: HscEnv -> Ms.MSpec BareType Symbol -> IO ([(Var, RefType)], [(Symbol, RefType)])
makeMeasureSpec env m = execBare mkSpec env
  where mkSpec = wrapErr "mkMeasureSort" mkMeasureSort m' >>= mkMeasureDCon >>= return . Ms.dataConTypes
        m'     = first (txTyVarBinds . mapReft ureft) m

makeAssumeSpec :: [Var] -> HscEnv -> RTEnv -> [(Symbol, BareType)] -> IO [(Var, SpecType)]
makeAssumeSpec vs env renv xbs = execBare mkAspec env
  where mkAspec = forM vbs (mkVarSpec renv) >>= return . checkAssumeSpec
        vbs     = joinIds vs (first symbolString <$> xbs) 

mkVarSpec renv (v, b) = liftM (v,) (wrapErr msg (mkSpecType renv) b)
  where msg = "mkVarSpec fails on " ++ showPpr v ++ " :: "  ++ showPpr b 

checkAssertSpec :: [Var] -> [(Symbol, BareType)] -> IO () 
checkAssertSpec vs xbs =
  let vm  = M.fromList [(showPpr v, v) | v <- vs] 
      xs' = [s | (x, _) <- xbs, let s = symbolString x, not (M.member s vm)]
  in case xs' of 
    [] -> return () 
    _  -> errorstar $ "Asserts for Unknown variables: "  ++ (intercalate ", " xs')  

-- joinIds :: [Var] -> [(String, a)] -> [(Var, a)]
joinIds vs xts = {-tracePpr "spec vars"-} vts   
  where vm     = M.fromList [(showPpr v, v) | v <- {-tracePpr "vars"-} vs]
        vts    = catMaybes [(, t) <$> (M.lookup x vm) | (x, t) <- {-tracePpr "bareVars"-} xts]

makeInvariants :: HscEnv -> [BareType] -> IO [SpecType]
makeInvariants env ts = execBare (mapM (mkSpecType M.empty) ts) env

mkSpecType re  = ofBareType' re      . txParams [] . txTyVarBinds . mapReft (bimap canonReft stringTyVarTy) 
mkPredType πs  = ofBareType' M.empty . txParams πs . txTyVarBinds . mapReft (fmap stringTyVarTy)


-----------------------------------------------------------------
------ Querying GHC for Id, Type, Class, Con etc. ---------------
-----------------------------------------------------------------

class Outputable a => GhcLookup a where
  lookupName :: HscEnv -> a -> IO (Maybe Name)
  candidates :: a -> [a]

instance GhcLookup String where
  lookupName     = stringLookup
  candidates x   = [x, swizzle x] 

swizzle =  dropModuleNames . stripParens

instance GhcLookup Name where
  lookupName _   = return . Just
  candidates x   = [x]

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
         _   -> throwError $ "lookupGhcThing unknown " ++ name ++ " : " ++ (showPpr x)
         -- _   -> liftIO $ ioError $ userError $ "lookupGhcThing unknown " ++ name ++ " : " ++ (showPpr x)

lookupGhcThing' :: (GhcLookup a) => String -> (TyThing -> Maybe b) -> a -> BareM (Maybe b)
lookupGhcThing' name f x 
  = do env     <- ask
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

------------------------------------------------------------------------
----------------- Transforming Raw Strings using GHC Env ---------------
------------------------------------------------------------------------

ofBareType' re = wrapErr "ofBareType" (liftM (expandRTAlias re) . ofBareType re)

ofBareType _ (RVar (RV a) r) 
  = return $ RVar (stringRTyVar a) r
ofBareType _ (RVar (RP π) r) 
  = return $ RVar (RP π) r
ofBareType re (RFun (RB x) t1 t2 _) 
  = liftM2 (rFun (RB x)) (ofBareType re t1) (ofBareType re t2)
ofBareType re (RAll (RV a) t) 
  = liftM  (RAll (stringRTyVar a)) (ofBareType re t)
ofBareType re (RAll (RP π) t) 
  = liftM  (RAll (RP π)) (ofBareType re t)
ofBareType re (RApp tc ts@[_] rs r) 
  | isList tc
  = liftM2 (bareTCApp r (Right listTyCon)) (forM rs $ ofRef re) (forM ts $ ofBareType re)
ofBareType re (RApp tc ts rs r) 
  | isTuple tc
  = liftM2 (bareTCApp r c) (forM rs $ ofRef re) (forM ts $ ofBareType re)
    where c = Right $ tupleTyCon BoxedTuple (length ts)
ofBareType re (RApp tc ts [] r)
  | tc `M.member` re
  = liftM (bareTCApp r (Left tc) []) (forM ts $ ofBareType re)
ofBareType re (RApp tc ts rs r)
  = liftM3 (bareTCApp r)  (Right <$> lookupGhcTyCon tc) (forM rs $ ofRef re) (forM ts $ ofBareType re)
ofBareType re (RCls c ts)
  = liftM2 RCls (lookupGhcClass c) (forM ts $ ofBareType re)

ofRef re (RPoly t)   
  = liftM RPoly (ofBareType re t)
ofRef re (RMono r) 
  = return (RMono r)

-- TODO: move back to RefType
bareTCApp r c rs ts 
  = {- tracePpr ("bareTCApp: t = " ++ show t) $ -}
    if isTrivial t0 then t' else t
    where t0 = RApp c' ts rs top
          t  = RApp c' ts rs r
          t' = (expandRTypeSynonyms t0) `strengthen` r
          c' = (`RTyCon` []) <$> c

expandRTypeSynonyms = ofType . expandTypeSynonyms . toType

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

mkMeasureSort (Ms.MSpec cm mm) 
  = liftM (Ms.MSpec cm) $ forM mm $ \m -> 
      liftM (\s' -> m {Ms.sort = s'}) (ofBareType' M.empty (Ms.sort m))

-----------------------------------------------------------------------
---------------- Bare Predicate: DataCon Definitions ------------------
-----------------------------------------------------------------------

makeConTypes :: HscEnv -> [DataDecl] -> IO ([(TyCon, TyConP)], [[(DataCon, DataConP)]])
makeConTypes env dcs = unzip <$> execBare (mapM ofBDataDecl dcs) env

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

txParams πs t = mapReft (substParg (txPvar (predMap πs t))) t

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
  -- not $ eqType' (toType t) (varType x) 

---------------------------------------------------------------------------------
----------------- Helper Predicates on Types ------------------------------------
---------------------------------------------------------------------------------

eqType' τ1 τ2 
  = -- tracePpr ("eqty: τ1 = " ++ showPpr τ1 ++ " τ2 = " ++ showPpr τ2) $ 
    eqType τ1 τ2 

eqShape :: SpecType -> SpecType -> Bool 
eqShape t1 t2 
  = -- tracePpr ("eqShape : t1 = " ++ showPpr t1 ++ " t2 = " ++ showPpr t2) $ 
    eqShape' t1 t2 

eqShape' (RAll (RP _) t) (RAll (RP _) t') 
  = eqShape t t'
eqShape' (RAll (RP _) t) t' 
  = eqShape t t'
eqShape' (RAll (RV α) t) (RAll (RV α') t')
  = eqShape t (subsTyVar_meet (α', RVar (RV α) top) t')
eqShape' (RFun _ t1 t2 _) (RFun _ t1' t2' _) 
  = eqShape t1 t1' && eqShape t2 t2'
eqShape' t@(RApp c ts _ _) t'@(RApp c' ts' _ _)
  =  ((c == c') && length ts == length ts' && and (zipWith eqShape ts ts'))
 -- || (eqType (toType t) (toType t'))
eqShape' (RCls c ts) (RCls c' ts')
  = (c == c') && length ts == length ts' && and (zipWith eqShape ts ts')
eqShape' (RVar (RV α) _) (RVar (RV α') _)
  = α == α' 
eqShape' t1 t2 
  = False

-------------------------------------------------------------------------------
----------- Refinement Type Aliases -------------------------------------------
-------------------------------------------------------------------------------

type ETyC      = Either String RTyCon
type RTEnv     = M.Map String (RTAlias RTyVar SpecType)
type RTEnvE    = M.Map String (RTAlias RTyVar SpecTypeE)
type SpecTypeE = RType Class ETyC RTyVar (PVar Type) (UReft Reft Type)

makeRTAliasEnv  :: HscEnv -> [RTAlias String BareType] -> IO RTEnv
makeRTAliasEnv = error "TODO"

-- expandRTAliasE  :: RTEnvE -> SpecTypeE -> SpecType
expandRTAliasE = go []
  where go = expandAlias go

-- expandRTAlias :: RTEnv -> SpecTypeE -> SpecType
expandRTAlias = go [] 
  where go = expandAlias (\_ _ -> id) 

expandAlias f s env = go s 
  where go s t@(RApp (Left c) ts [] r)    
          | c `elem` s                = errorstar $ "Cyclic Reftype Alias Definition: " ++ show (c:s)
          | otherwise                 = expandRTApp (f (c:s) env) env s c ts r
        go s (RApp (Right c) ts rs r) = RApp c (go s <$> ts) (go' s <$> rs) r 
        go s (RAll a t)               = RAll a (go s t)
        go s (RFun x t t' r)          = RFun x (go s t) (go s t') r
        go s (RCls c ts)              = RCls c (go s <$> ts) 
        go s t                        = t
        go' s (RMono r)               = RMono r

expandRTApp tx env s c ts r
  = case M.lookup c env of
      Nothing  -> errorstar $ "Aargh. Unknown Reftype Alias" ++ c 
      Just rta -> subsTyVars_meet αts t' `strengthen` r
                  where t'  = tx (rtBody rta) 
                        αts = Ex.assert (length αs == length ts) $ zip αs ts
                        αs  = rtArgs rta

-- expandRTAliasE =
--  where go s t@(RApp (Left c) ts [] r)    
--          | c `elem` s                = errorstar $ "Cyclic Reftype Alias Definition: " ++ show (c:s)
--          | otherwise                 = expandRTApp (expandRTAliasE (c:s) env) env s c ts r
--        go s (RApp (Right c) ts rs r) = RApp c (go s <$> ts) (go' s <$> rs) r 
--        go s (RAll a t)               = RAll a (go s t)
--        go s (RFun x t t' r)          = RFun x (go s t) (go s t') r
--        go s (RCls c ts)              = RCls c (go s <$> ts) 
--        go s t                        = t
--        go' s (RMono r)               = RMono r


-- makeRTAliasEnv rtas 
-- expandRTAliases  :: Spec SpecType Symbol -> Spec SpecType Symbol
-- expandRTAliases sp 
--   = first (expandRTAlias env) sp
--     where env = safeFromList "Reftype Aliases" [(rtName x, x) | x <- aliases sp]



