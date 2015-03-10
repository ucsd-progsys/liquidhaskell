{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.Spec (
    makeClasses
  , makeQualifiers
  
  , makeHints
  , makeLVar
  , makeLazy
  , makeHIMeas
  , makeTExpr

  , makeTargetVars
  , makeAssertSpec
  , makeAssumeSpec
  , makeDefaultMethods

  , makeIAliases
  , makeInvariants

  , makeSpecDictionaries
  ) where

import MonadUtils (mapMaybeM)
import TyCon
import Var

import Control.Applicative ((<$>))
import Control.Monad.Error
import Control.Monad.State
import Data.Maybe
import Data.Monoid

import qualified Data.List           as L
import qualified Data.HashSet        as S
import qualified Data.HashMap.Strict as M

import Language.Fixpoint.Misc (concatMapM, group, mapFst, snd3)
import Language.Fixpoint.Names (dropModuleNames, dropSym, isPrefixOfSym, qualifySymbol, symbolString, takeModuleNames)
import Language.Fixpoint.Types (Qualifier(..), symbol)

import Language.Haskell.Liquid.Dictionaries
import Language.Haskell.Liquid.GhcMisc (getSourcePos, showPpr, symbolTyVar)
import Language.Haskell.Liquid.Misc (addFst3, fourth4)
import Language.Haskell.Liquid.RefType (generalize, rVar, symbolRTyVar)
import Language.Haskell.Liquid.Types

import qualified Language.Haskell.Liquid.Measure as Ms

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Existential
import Language.Haskell.Liquid.Bare.Lookup
import Language.Haskell.Liquid.Bare.Misc (joinVar)
import Language.Haskell.Liquid.Bare.OfType
import Language.Haskell.Liquid.Bare.Resolve
import Language.Haskell.Liquid.Bare.SymSort

makeClasses cmod cfg vs (mod, spec) = inModule mod $ mapM mkClass $ Ms.classes spec
  where
    --FIXME: cleanup this code
    unClass = snd . bkClass . fourth4 . bkUniv
    mkClass (RClass c ss as ms)
            = do let l   = loc c  
                 tc  <- lookupGhcTyCon c
                 ss' <- mapM (mkSpecType l) ss
                 let (dc:_) = tyConDataCons tc
                 let αs  = map symbolRTyVar as
                 let as' = [rVar $ symbolTyVar a | a <- as ]
                 let ms' = [ (s, rFun "" (RApp c (flip RVar mempty <$> as) [] mempty) t) | (s, t) <- ms]
                 vts <- makeSpec (noCheckUnknown cfg || cmod /= mod) vs ms'
                 let sts = [(val s, unClass $ val t) | (s, _)    <- ms
                                                     | (_, _, t) <- vts]
                 let t   = rCls tc as'
                 let dcp = DataConP l αs [] [] ss' (reverse sts) t
                 return ((dc,dcp),vts)

makeQualifiers (mod,spec) = inModule mod mkQuals
  where
    mkQuals = mapM (\q -> resolve (q_pos q) q) $ Ms.qualifiers spec

makeHints vs spec = varSymbols id vs $ Ms.decr spec
makeLVar  vs spec = fmap fst <$> (varSymbols id vs $ [(v, ()) | v <- Ms.lvars spec])
makeLazy  vs spec = fmap fst <$> (varSymbols id vs $ [(v, ()) | v <- S.toList $ Ms.lazy spec])
makeHIMeas vs spec = fmap (uncurry $ flip Loc) <$> (varSymbols id vs $ [(v, loc v) | v <- (S.toList $ Ms.hmeas spec) ++ (S.toList $ Ms.inlines spec)])
makeTExpr vs spec = varSymbols id vs $ Ms.termexprs spec

varSymbols :: ([Var] -> [Var]) -> [Var] -> [(LocSymbol, a)] -> BareM [(Var, a)]
varSymbols f vs  = concatMapM go
  where lvs        = M.map L.sort $ group [(sym v, locVar v) | v <- vs]
        sym        = dropModuleNames . symbol . showPpr
        locVar v   = (getSourcePos v, v)
        go (s, ns) = case M.lookup (val s) lvs of 
                     Just lvs -> return ((, ns) <$> varsAfter f s lvs)
                     Nothing  -> ((:[]).(,ns)) <$> lookupGhcVar s

varsAfter f s lvs 
  | eqList (fst <$> lvs)    = f (snd <$> lvs)
  | otherwise               = map snd $ takeEqLoc $ dropLeLoc lvs
  where
    takeEqLoc xs@((l, _):_) = L.takeWhile ((l==) . fst) xs
    takeEqLoc []            = []
    dropLeLoc               = L.dropWhile ((loc s >) . fst)
    eqList []               = True
    eqList (x:xs)           = all (==x) xs


------------------------------------------------------------------
-- | API: Bare Refinement Types ----------------------------------
------------------------------------------------------------------

makeTargetVars :: ModName -> [Var] -> [String] -> BareM [Var]
makeTargetVars name vs ss
  = do env   <- gets hscEnv
       ns    <- liftIO $ concatMapM (lookupName env name . dummyLoc . prefix) ss
       return $ filter ((`elem` ns) . varName) vs
    where
       prefix s = qualifySymbol (symbol name) (symbol s)


makeAssertSpec cmod cfg vs lvs (mod,spec)
  | cmod == mod
  = makeLocalSpec cfg cmod vs lvs (grepClassAsserts (Ms.rinstance spec)) (Ms.sigs spec ++ Ms.localSigs spec)
  | otherwise
  = inModule mod $ makeSpec True vs $ Ms.sigs spec

makeAssumeSpec cmod cfg vs lvs (mod,spec)
  | cmod == mod
  = makeLocalSpec cfg cmod vs lvs [] $ Ms.asmSigs spec
  | otherwise
  = inModule mod $ makeSpec True vs $ Ms.asmSigs spec

grepClassAsserts  = concatMap go 
   where
    go    = map goOne . risigs
    goOne = mapFst (fmap (symbol . (".$c" ++ ) . symbolString))


makeDefaultMethods :: [Var] -> [(ModName,Var,Located SpecType)]
                   -> [(ModName,Var,Located SpecType)]
makeDefaultMethods defVs sigs
  = [ (m,dmv,t)
    | dmv <- defVs
    , let dm = symbol $ showPpr dmv
    , "$dm" `isPrefixOfSym` (dropModuleNames dm)
    , let mod = takeModuleNames dm
    , let method = qualifySymbol mod $ dropSym 3 (dropModuleNames dm)
    , let mb = L.find ((method `isPrefixOfSym`) . symbol . snd3) sigs
    , isJust mb
    , let Just (m,_,t) = mb
    ]

makeLocalSpec :: Config -> ModName -> [Var] -> [Var] -> [(LocSymbol, BareType)] -> [(LocSymbol, BareType)]
                    -> BareM [(ModName, Var, Located SpecType)]
makeLocalSpec cfg mod vs lvs cbs xbs
  = do vbs1  <- fmap expand3 <$> varSymbols fchoose lvs (dupSnd <$> xbs1)
       vts1  <- map (addFst3 mod) <$> mapM mkVarSpec vbs1
       vts2  <- makeSpec (noCheckUnknown cfg) vs xbs2
       return $ vts1 ++ vts2
  where
    xbs1 = xbs1' ++ cbs
    (xbs1', xbs2)       = L.partition (modElem mod . fst) xbs
    dupSnd (x, y)       = (dropMod x, (x, y))
    expand3 (x, (y, w)) = (x, y, w)
    dropMod             = fmap (dropModuleNames . symbol)
    fchoose ls          = maybe ls (:[]) $ L.find (`elem` vs) ls
    modElem n x         = (takeModuleNames $ val x) == (symbol n)

makeSpec :: Bool -> [Var] -> [(LocSymbol, BareType)]
                 -> BareM [(ModName, Var, Located SpecType)]
makeSpec ignoreUnknown vs xbs
  = do vbs <- map (joinVar vs) <$> lookupIds ignoreUnknown xbs
       (BE { modName = mod}) <- get
       map (addFst3 mod) <$> mapM mkVarSpec vbs


lookupIds ignoreUnknown
  = mapMaybeM lookup
  where
    lookup (s, t)
      = (Just . (,s,t) <$> lookupGhcVar s) `catchError` handleError
    handleError (ErrGhc {})
      | ignoreUnknown
        = return Nothing
    handleError err
      = throwError err

mkVarSpec :: (Var, LocSymbol, BareType) -> BareM (Var, Located SpecType)
mkVarSpec (v, Loc l _, b) = tx <$> mkSpecType l b
  where
    tx = (v,) . Loc l . generalize


makeIAliases (mod, spec)
  = inModule mod $ makeIAliases' $ Ms.ialiases spec

makeIAliases' :: [(Located BareType, Located BareType)] -> BareM [(Located SpecType, Located SpecType)]
makeIAliases' ts = mapM mkIA ts
  where 
    mkIA (t1, t2)      = liftM2 (,) (mkI t1) (mkI t2)
    mkI (Loc l t)      = (Loc l) . generalize <$> mkSpecType l t

makeInvariants (mod,spec)
  = inModule mod $ makeInvariants' $ Ms.invariants spec

makeInvariants' :: [Located BareType] -> BareM [Located SpecType]
makeInvariants' ts = mapM mkI ts
  where 
    mkI (Loc l t)  = (Loc l) . generalize <$> mkSpecType l t


makeSpecDictionaries embs vars specs sp
  = do ds <- (dfromList . concat)  <$>  mapM (makeSpecDictionary embs vars) specs
       return $ sp {dicts = ds}

makeSpecDictionary embs vars (_, spec)  
  = mapM (makeSpecDictionaryOne embs vars) (Ms.rinstance spec)

makeSpecDictionaryOne embs vars (RI x t xts) 
  = do t'  <-  mkTy t
       tyi <- gets tcEnv
       ts' <- (map (txRefSort tyi embs . txExpToBind)) <$> mapM mkTy' ts
       let (d, dts) = makeDictionary $ RI x t' $ zip xs ts'
       let v = lookupName d   
       return (v, dts)
  where 
    mkTy  t  = mkSpecType (loc x) t
    mkTy' t  = generalize  <$> mkTy t
    (xs, ts) = unzip xts
    lookupName x 
             = case filter ((==x) . fst) ((\x -> (dropModuleNames $ symbol $ show x, x)) <$> vars) of 
                [(_, x)] -> x
                _ -> head vars -- HACK, but since it is not imported, 
                               -- the dictionary cannot be used
                               -- errorstar ("makeSpecDictionary: " ++ show x ++ "\tnot in\n" ++ show vars)

