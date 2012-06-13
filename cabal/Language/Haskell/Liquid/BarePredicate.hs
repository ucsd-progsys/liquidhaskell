{-# LANGUAGE NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, ScopedTypeVariables  #-}
module Language.Haskell.Liquid.BarePredicate where

import CoreSyn
import Data.HashTable as HT

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



data PredicateB = PBF String String [(String, String)]
                | PB String [String]
                | PBTrue
                | PBAnd PredicateB PredicateB 
                deriving (Eq, Show)

data PrTypeP = PrPairP (PredicateB, String)
            | PrPredTyP String [PrTypeP]             
            | PrAppTyP String PrTypeP PrTypeP            
            | PrForAllPrP [PredicateB] PrTypeP       
            | PrForAllTyP String PrTypeP             
            | PrTyConAppP String [PrTypeP] [PredicateB] PredicateB
            | PrLstP PrTypeP
            | PrIntP PredicateB
            | PrTupP [PrTypeP]
              deriving Show


data DataDecl 
  = D String [String] [PredicateB] [(String, [(String, PrTypeP)])] deriving Show


ofBDataCon tyCon aps vs preds (c, xts)
 = do c' <- lookupGhcDataCon c
      ts' <- mapM (ofPType aps) ts
      let t0 = PrTyCon tyCon (map ((flip PrVar) PdTrue) vs) preds PdTrue
      let t2 = foldl (\t' (x,t)-> PrFun x t t') t0 (zip xs' ts')
      let t1 = foldl (flip PrAllPr) t2 preds
      let t  = foldl (flip PrAll) t1 vs
      return $ (c', DataConP vs (preds) (reverse (zip xs' ts')) t0) 
 where (xs, ts) = unzip xts
       xs'      = map stringSymbol xs
 



ofBDataDecl (D tyCon vars ps cts)
  = do c <- lookupGhcTyCon tyCon 
       cs <- mapM (ofBDataCon c (avs, ps') vs preds) cts
       return $ ((c, TyConP vs preds), cs)
 where  vs = map stringTyVar vars
        avs = zip vars vs
        ps' = map (ofBPredicate_ avs) ps
        preds = snd $ unzip ps'



ofBPredicate _ (PBTrue) = PdTrue
ofBPredicate avs (PBAnd p1 p2) 
 = PdAnd (ofBPredicate avs p1) (ofBPredicate avs p2) 
ofBPredicate avs (PBF s as xs) 
  = PdVar $ PV { pname = stringSymbol s
               , ptype = f as
               , pargs = map (ofArgsD (fst avs)) xs
               }
  where f v = let v':_ = [v | (a, v) <- fst avs, a==s ] in TyVarTy v'
ofBPredicate avs (PB s xs) 
  = PdVar $ PV { pname = stringSymbol s
               , ptype = ptype f 
               , pargs = args
               }
  where f = head [ v | (a, PdVar v) <- snd avs, a==s]
        args = zipWith (\(t, x1, _) x-> (t, x1, stringSymbol x))(pargs f) xs

wiredIn :: M.Map String Name
wiredIn = M.fromList $
  [ ("GHC.Integer.smallInteger" , smallIntegerName) 
  , ("GHC.Num.fromInteger", fromIntegerName)
  , ("GHC.Types.I#" , dataConName intDataCon)
  , ("GHC.Prim.Int#", TC.tyConName intPrimTyCon) ]
 


mkConTypes env dcs = runReaderT mkCon env
  where mkCon = forM dcs ofBDataDecl

mkPredType env xbs = runReaderT mkPred env
  where mkPred = forM xbs $ \(x, b) -> liftM2 (,) (lookupGhcId (symbolString x)) (mkPType b)

mkPType =  ofPType ([], [])

ofArgsD vs (x, va) = (TyVarTy t, x', x')
  where t:_ = [vt| (a, vt) <- vs, a==va]
        x'  = stringSymbol x

ofBPredicate_ vs (PBF x va xs)
  = (x, PdVar $ PV { pname = stringSymbol x
                   , ptype = TyVarTy t
                   , pargs = map (ofArgsD vs) xs
                   })
  where t:_ = [vt| (a, vt) <- vs, a==va]

--ofPType :: ([(String, TyVar)], [(String, Predicate)]) ->PrTypeP -> m PrType
ofPType (as, ps) (PrForAllTyP a t) = 
   let v = stringTyVar a
   in do nt <- ofPType ((a, v):as, ps) t 
         return $ PrAll v nt

ofPType (vs, ps) (PrForAllPrP pst t) = 
   do nt <- ofPType (vs, ps++ps') t
      return $ foldl (\t p -> PrAllPr p t) nt (snd $ unzip ps') 
  where ps' = map (ofBPredicate_ vs) pst

ofPType as (PrAppTyP x t1 t2) = 
   do  nt1 <- ofPType as t1                    
       nt2 <- ofPType as t2
       return $ PrFun (stringSymbol x) nt1 nt2

ofPType as (PrPairP(p,s)) = 
   let (v):_ = [v | (a, v)<-fst as, a==s] in
   return $ PrVar v (ofBPredicate as p)

ofPType as (PrLstP t) =
   do nt <- ofPType as t
      return $  PrTyCon listTyCon [nt] [] PdTrue

ofPType as (PrIntP p) 
  = return $ PrTyCon intTyCon [] [] (ofBPredicate as p)

ofPType as (PrTupP [t]) = ofPType as t
ofPType as (PrTupP ts) = 
   do nts <- mapM (ofPType as) ts
      let c = tupleTyCon BoxedTuple (length ts)
       in return $ PrTyCon c nts [] PdTrue
ofPType as (PrTyConAppP s ts ps p) = 
  do c <- lookupGhcTyCon s
     nts <- mapM (ofPType as) ts
     return $ PrTyCon c nts (map (ofBPredicate as) ps) (ofBPredicate as p)
ofPType as (PrPredTyP s ts) = 
  do c <- lookupGhcClass s 
     nts <- mapM (ofPType as) ts
     return $ PrClass c nts
{-
doParse specPr

            | PrPredTyP String [PrTypeP]             
            | PrTyConAppP String [PrTypeP] Predicate

data PrType = PrPair (Predicate, Type)
            | PrPredTy PredType              
            | PrAppTy PrType PrType            
            | PrForAllPr [Predicate] PrType       
            | PrTyConApp TyCon [PrType] Predicate 
-}

stringTyVar :: String -> TyVar
stringTyVar s = mkTyVar name liftedTypeKind
  where name = mkInternalName initTyVarUnique occ noSrcSpan 
        occ  = mkTyVarOcc s



-----------------------------------------------------------------
------ Querying GHC for Id, Type, Class, Con etc. ---------------
-----------------------------------------------------------------

class Outputable a => GhcLookup a where
  lookupName :: HscEnv -> a -> IO Name

instance GhcLookup String where
  lookupName = stringToName

instance GhcLookup Name where
  lookupName _  = return

--lookupGhcThing :: (GhcLookup a) => String -> (TyThing -> Maybe b) -> a -> b
lookupGhcThing name f x 
  = do env     <- ask
       (_,res) <- liftIO $ tcRnLookupName env =<< lookupName env x
       case f `fmap` res of
         Just (Just z) -> 
           return z
         _      -> 
           liftIO $ ioError $ userError $ "lookupGhcThing unknown " ++ name ++ " : " ++ (showPpr x)

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
           _          -> error $ "PredBare.lookupName cannot find name for: " ++ s


