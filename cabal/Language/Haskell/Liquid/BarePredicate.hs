{-# LANGUAGE NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, ScopedTypeVariables  #-}
module Language.Haskell.Liquid.BarePredicate where

import CoreSyn
-- import Data.HashTable as HT

import Type 
import Literal
import Data.List 	(head, nub, elem, foldl', union, sort)
import Name             (mkInternalName)
import OccName          (mkTyVarOcc)
import Unique           (getKey, getUnique, initTyVarUnique)
import SrcLoc 		      (noSrcSpan)
import TypeRep
import Class
import qualified TyCon as TC
import TyCon
import Coercion         
--import Pair    
import DataCon

import GHC hiding (lookupName)	
import Outputable
import Var
import PrelNames

import HscTypes   (HscEnv)
import qualified CoreMonad as CM 
import GHC.Paths (libdir)

import System.Environment (getArgs)
import DynFlags (defaultDynFlags)
import HscMain
import TypeRep
import TysWiredIn
import BasicTypes (TupleSort(..), Boxity (..))
import TcRnDriver (tcRnLookupRdrName, tcRnLookupName) 

import TysPrim          (intPrimTyCon)
import TysWiredIn       (listTyCon, intTy, intTyCon, boolTyCon, intDataCon, trueDataCon, falseDataCon)


import Data.List (sort)
import Data.Char (isUpper)
import ErrUtils
-- import Control.Monad
import Data.Traversable (forM)
import Control.Applicative  ((<$>))
import Control.Monad.Reader hiding (forM)
import Data.Generics.Schemes
import Data.Generics.Aliases
import Data.Data hiding (TyCon)
import qualified Data.Map as M

import Language.Haskell.Liquid.Fixpoint hiding (PTrue, PAnd)
import Language.Haskell.Liquid.RefType
import qualified Language.Haskell.Liquid.Measure as Ms
import Language.Haskell.Liquid.Misc
import qualified Control.Exception as Ex
import Language.Haskell.Liquid.PredType


ofBPredicate :: ([(String, Var)], [(String, PVar Type)]) -> PredicateB -> Predicate Type
ofBPredicate _ (PBTrue) 
  = pdTrue
ofBPredicate avs (PBAnd p1 p2) 
  = pdAnd $ ofBPredicate avs <$> [p1, p2] 
ofBPredicate avs (PBF s as xs) 
  = pdVar $ PV { pname = stringSymbol s
               , ptype = f as
               , pargs = map (ofArgsD (fst avs)) xs
               }
  where f v = let v':_ = [v | (a, v) <- fst avs, a == s ] in TyVarTy v'

ofBPredicate avs (PB s xs) 
  = pdVar $ PV { pname = stringSymbol s
               , ptype = ptype f 
               , pargs = args
               }
  where f = head [ v | (a, v) <- snd avs, a==s]
        args = zipWith (\(t, x1, _) x -> (t, x1, stringSymbol x)) (pargs f) xs


mkPredType env xbs = runReaderT mkPred env
  where mkPred = forM xbs $ \(x, b) -> liftM2 (,) (lookupGhcId (symbolString x)) (mkPType b)

mkPType =  ofPType ([], [])

ofArgsD (x, a) = (TyVarTy α, x', x')
  where α  = stringTyVar a
        x' = stringSymbol x

--ofArgsD vs (x, va) = (TyVarTy t, x', x')
--  where t:_ = [vt| (a, vt) <- vs, a == va]
--        x'  = stringSymbol x

ofBPredicate_ vs (PBF x va xs)
  = (x, PV { pname = stringSymbol x
           , ptype = TyVarTy t
           , pargs = map (ofArgsD vs) xs
           })
  where t:_ = [ vt | (a, vt) <- vs, a == va ]

--ofPType :: ([(String, TyVar)], [(String, Predicate)]) -> PrTypeP -> m PrType
ofPType (as, ps) (PrForAllTyP a t) = 
   let v = stringTyVar a
   in do nt <- ofPType ((a, v):as, ps) t 
         return $ RAll (RV v) nt

ofPType (as, ps) (PrForAllPrP pst t) = 
   do nt <- ofPType (as, ps ++ ps') t
      return $ foldl (\t pv -> RAll (RP pv) t) nt (snd $ unzip ps') 
  where ps' = map (ofBPredicate_ as) pst

ofPType as (PrAppTyP x t1 t2) = 
   do  nt1 <- ofPType as t1                    
       nt2 <- ofPType as t2
       return $ RFun (RB $ stringSymbol x) nt1 nt2

ofPType as (PrPairP (p, s)) = 
   let (v):_ = [v | (a, v) <- fst as, a == s ] in
   return $ RVar (RV v) (ofBPredicate as p)

ofPType as (PrLstP t) =
   do nt <- ofPType as t
      return $ RApp (RTyCon listTyCon []) [nt] [] pdTrue

ofPType as (PrIntP p) 
  = return $ RApp (RTyCon intTyCon []) [] [] (ofBPredicate as p)

ofPType as (PrTupP [t]) 
  = ofPType as t

ofPType as (PrTupP ts) = 
   do nts <- mapM (ofPType as) ts
      let c = tupleTyCon BoxedTuple (length ts)
       in return $ RApp (RTyCon c []) nts [] pdTrue

ofPType as (PrTyConAppP s ts ps p) = 
  do c <- lookupGhcTyCon s
     nts <- mapM (ofPType as) ts
     return $ RApp (RTyCon c []) nts (map (ofBPredicate as) ps) (ofBPredicate as p)

ofPType as (PrPredTyP s ts) = 
  do c <- lookupGhcClass s 
     nts <- mapM (ofPType as) ts
     return $ RCls c nts

--stringTyVar :: String -> TyVar
--stringTyVar s = mkTyVar name liftedTypeKind
--  where name = mkInternalName initTyVarUnique occ noSrcSpan 
--        occ  = mkTyVarOcc s


-----------------------------------------------------------------
------ Querying GHC for Id, Type, Class, Con etc. ---------------
-----------------------------------------------------------------

--class Outputable a => GhcLookup a where
--  lookupName :: HscEnv -> a -> IO Name
--
--instance GhcLookup String where
--  lookupName = stringToName
--
--instance GhcLookup Name where
--  lookupName _  = return
--
----lookupGhcThing :: (GhcLookup a) => String -> (TyThing -> Maybe b) -> a -> b
--lookupGhcThing name f x 
--  = do env     <- ask
--       (_,res) <- liftIO $ tcRnLookupName env =<< lookupName env x
--       case f `fmap` res of
--         Just (Just z) -> 
--           return z
--         _      -> 
--           liftIO $ ioError $ userError $ "lookupGhcThing unknown " ++ name ++ " : " ++ (showPpr x)
--
--lookupGhcTyCon = lookupGhcThing "TyCon" ftc 
--  where ftc (ATyCon x) = Just x
--        ftc _          = Nothing
--
--lookupGhcClass = lookupGhcThing "Class" ftc 
--  where ftc (ATyCon x) = tyConClass_maybe x
--        ftc _          = Nothing
--
--lookupGhcDataCon = lookupGhcThing "DataCon" fdc 
--  where fdc (ADataCon x) = Just x
--        fdc _            = Nothing
--
--lookupGhcId s 
--  = lookupGhcThing "Id" fid s
--  where fid (AnId x)     = Just x
--        fid (ADataCon x) = Just $ dataConWorkId x
--        fid _            = Nothing
--
--wiredIn :: M.Map String Name
--wiredIn = M.fromList $
--  [ ("GHC.Integer.smallInteger" , smallIntegerName) 
--  , ("GHC.Num.fromInteger", fromIntegerName)
--  , ("GHC.Types.I#" , dataConName intDataCon)
--  , ("GHC.Prim.Int#", TC.tyConName intPrimTyCon) ]
--
--stringToName :: HscEnv -> String -> IO Name
--stringToName env k 
--  = case M.lookup k wiredIn of 
--      Just n  -> return n
--      Nothing -> stringToNameEnv env k
--
--stringToNameEnv :: HscEnv -> String -> IO Name
--stringToNameEnv env s 
--    = do L _ rn         <- hscParseIdentifier env s
--         (_, lookupres) <- tcRnLookupRdrName env rn
--         case lookupres of
--           Just (n:_) -> return n
--           _          -> error $ "PredBare.lookupName cannot find name for: " ++ s
