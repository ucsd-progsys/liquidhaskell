{-# LANGUAGE FlexibleContexts         #-}
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
  , makeBounds
  , makeHBounds
  ) where

import Prelude hiding (error)
import MonadUtils (mapMaybeM)
import TyCon
import Var
import CoreSyn (CoreBind)


import Control.Monad.Except
import Control.Monad.State
import Data.Maybe


import qualified Data.List           as L
import qualified Data.HashSet        as S
import qualified Data.HashMap.Strict as M

import           Language.Fixpoint.Misc (group, snd3)
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types.Dictionaries
import           Language.Haskell.Liquid.GHC.Misc ( dropModuleNames, qualifySymbol, takeModuleNames, getSourcePos, showPpr, symbolTyVar)
import           Language.Haskell.Liquid.Misc (addFst3, fourth4, mapFst, concatMapM)
import           Language.Haskell.Liquid.Types.RefType (generalize, rVar, symbolRTyVar)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.Bounds

import qualified Language.Haskell.Liquid.Measure as Ms

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Existential
import Language.Haskell.Liquid.Bare.Lookup
import Language.Haskell.Liquid.Bare.Misc (joinVar)
import Language.Haskell.Liquid.Bare.OfType
import Language.Haskell.Liquid.Bare.Resolve
import Language.Haskell.Liquid.Bare.SymSort
import Language.Haskell.Liquid.Bare.Measure

makeClasses cmod cfg vs (mod, spec) = inModule mod $ mapM mkClass $ Ms.classes spec
  where
    --FIXME: cleanup this code
    unClass = snd . bkClass . fourth4 . bkUniv
    mkClass (RClass c ss as ms)
            = do let l      = loc  c
                 let l'     = locE c
                 tc        <- lookupGhcTyCon c
                 ss'       <- mapM mkLSpecType ss
                 let (dc:_) = tyConDataCons tc
                 let αs  = map symbolRTyVar as
                 let as' = [rVar $ symbolTyVar a | a <- as ]
                 let ms' = [ (s, rFun "" (RApp c (flip RVar mempty <$> as) [] mempty) <$> t) | (s, t) <- ms]
                 vts <- makeSpec (noCheckUnknown cfg || cmod /= mod) vs ms'
                 let sts = [(val s, unClass $ val t) | (s, _)    <- ms
                                                     | (_, _, t) <- vts]
                 let t   = rCls tc as'
                 let dcp = DataConP l αs [] [] (val <$> ss') (reverse sts) t l'
                 return ((dc,dcp),vts)

makeQualifiers (mod,spec) = inModule mod mkQuals
  where
    mkQuals = mapM (\q -> resolve (F.q_pos q) q) $ Ms.qualifiers spec

makeHints   vs spec = varSymbols id vs $ Ms.decr spec
makeLVar    vs spec = fmap fst <$> varSymbols id vs [(v, ()) | v <- Ms.lvars spec]
makeLazy    vs spec = fmap fst <$> varSymbols id vs [(v, ()) | v <- S.toList $ Ms.lazy spec]
makeHBounds vs spec = varSymbols id vs [(v, v ) | v <- S.toList $ Ms.hbounds spec]
makeTExpr   vs spec = varSymbols id vs $ Ms.termexprs spec
makeHIMeas  vs spec = fmap tx <$> varSymbols id vs [(v, (loc v, locE v)) | v <- S.toList (Ms.hmeas spec) ++ S.toList (Ms.inlines spec)]
  where
    tx (x,(l, l'))  = Loc l l' x

varSymbols :: ([Var] -> [Var]) -> [Var] -> [(LocSymbol, a)] -> BareM [(Var, a)]
varSymbols f vs  = concatMapM go
  where lvs        = M.map L.sort $ group [(sym v, locVar v) | v <- vs]
        sym        = dropModuleNames . F.symbol . showPpr
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
       prefix s = qualifySymbol (F.symbol name) (F.symbol s)

makeAssertSpec :: ModName -> Config -> [Var] -> [Var] -> (ModName, Ms.BareSpec)
               -> BareM [(ModName, Var, LocSpecType)]
makeAssertSpec cmod cfg vs lvs (mod, spec)
  | cmod == mod
  = makeLocalSpec cfg cmod vs lvs (grepClassAsserts (Ms.rinstance spec)) (Ms.sigs spec ++ Ms.localSigs spec)
  | otherwise
  = inModule mod $ makeSpec True vs $ Ms.sigs spec

makeAssumeSpec :: ModName -> Config -> [Var] -> [Var] -> (ModName, Ms.BareSpec)
               -> BareM [(ModName, Var, LocSpecType)]
makeAssumeSpec cmod cfg vs lvs (mod, spec)
  | cmod == mod
  = makeLocalSpec cfg cmod vs lvs [] $ Ms.asmSigs spec
  | otherwise
  = inModule mod $ makeSpec True vs  $ Ms.asmSigs spec

grepClassAsserts  = concatMap go
   where
    go    = map goOne . risigs
    goOne = mapFst (fmap (F.symbol . (".$c" ++ ) . F.symbolString))


makeDefaultMethods :: [Var] -> [(ModName,Var,Located SpecType)]
                   -> [(ModName, Var ,Located SpecType)]
makeDefaultMethods defVs sigs
  = [ (m,dmv,t)
    | dmv <- defVs
    , let dm = F.symbol $ showPpr dmv
    , "$dm" `F.isPrefixOfSym` dropModuleNames dm
    , let mod = takeModuleNames dm
    , let method = qualifySymbol mod $ F.dropSym 3 (dropModuleNames dm)
    , let mb = L.find ((method `F.isPrefixOfSym`) . F.symbol . snd3) sigs
    , isJust mb
    , let Just (m,_,t) = mb
    ]

makeLocalSpec :: Config -> ModName -> [Var] -> [Var]
              -> [(LocSymbol, Located BareType)]
              -> [(LocSymbol, Located BareType)]
              -> BareM [(ModName, Var, Located SpecType)]
makeLocalSpec cfg mod vs lvs cbs xbs
  = do vbs1  <- fmap expand3 <$> varSymbols fchoose lvs (dupSnd <$> xbs1)
       vts1  <- map (addFst3 mod) <$> mapM mkVarSpec vbs1
       vts2  <- makeSpec (noCheckUnknown cfg) vs xbs2
       return $ vts1 ++ vts2
  where
    xbs1                = xbs1' ++ cbs
    (xbs1', xbs2)       = L.partition (modElem mod . fst) xbs
    dupSnd (x, y)       = (dropMod x, (x, y))
    expand3 (x, (y, w)) = (x, y, w)
    dropMod             = fmap (dropModuleNames . F.symbol)
    fchoose ls          = maybe ls (:[]) $ L.find (`elem` vs) ls
    modElem n x         = takeModuleNames (val x) == F.symbol n

makeSpec :: Bool -> [Var] -> [(LocSymbol, Located BareType)]
         -> BareM [(ModName, Var, LocSpecType)]
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

mkVarSpec :: (Var, LocSymbol, Located BareType) -> BareM (Var, Located SpecType)
mkVarSpec (v, _, b) = tx <$> mkLSpecType b
  where
    tx              = (v,) . fmap generalize

makeIAliases (mod, spec)
  = inModule mod $ makeIAliases' $ Ms.ialiases spec

makeIAliases' :: [(Located BareType, Located BareType)] -> BareM [(Located SpecType, Located SpecType)]
makeIAliases'     = mapM mkIA
  where
    mkIA (t1, t2) = (,) <$> mkI t1 <*> mkI t2
    mkI t         = fmap generalize <$> mkLSpecType t

makeInvariants (mod,spec)
  = inModule mod $ makeInvariants' $ Ms.invariants spec

makeInvariants' :: [Located BareType] -> BareM [Located SpecType]
makeInvariants' = mapM mkI
  where
    mkI t       = fmap generalize <$> mkLSpecType t

makeSpecDictionaries :: F.TCEmb TyCon -> [Var] -> [(a, Ms.BareSpec)] -> GhcSpec
                     -> BareM GhcSpec
makeSpecDictionaries embs vars specs sp
  = do ds <- (dfromList . concat)  <$>  mapM (makeSpecDictionary embs vars) specs
       return $ sp { dicts = ds }

makeSpecDictionary :: F.TCEmb TyCon -> [Var] -> (a, Ms.BareSpec)
                   -> BareM [(Var, M.HashMap F.Symbol SpecType)]
makeSpecDictionary embs vars (_, spec)
  = catMaybes <$> mapM (makeSpecDictionaryOne embs vars) (Ms.rinstance spec)

makeSpecDictionaryOne :: F.TCEmb TyCon -> [Var] -> RInstance (Located BareType)
                      -> BareM (Maybe (Var, M.HashMap F.Symbol SpecType))
makeSpecDictionaryOne embs vars (RI x t xts)
  = do t'  <- mkLSpecType t
       tyi <- gets tcEnv
       ts' <- map (val . txRefSort tyi embs . fmap txExpToBind) <$> mapM mkTy' ts
       let (d, dts) = makeDictionary $ RI x (val t') $ zip xs ts'
       let v = lookupName d
       return ((, dts) <$> v)
  where
    mkTy' t  = fmap generalize <$> mkLSpecType t
    (xs, ts) = unzip xts
    lookupName x
             = case filter ((==x) . fst) ((\x -> (dropModuleNames $ F.symbol $ show x, x)) <$> vars) of
                [(_, x)] -> Just x
                _        -> Nothing

makeBounds ::  F.TCEmb TyCon -> ModName -> [Var] -> [CoreBind] -> [(ModName, Ms.BareSpec)] -> BareM ()
makeBounds tce name defVars cbs specs
  = do bnames  <- mkThing makeHBounds
       hbounds <- makeHaskellBounds tce cbs bnames
       bnds    <- M.fromList <$> mapM go (concatMap (M.toList . Ms.bounds . snd ) specs)
       modify   $ \env -> env { bounds = hbounds `mappend` bnds }
  where
    go (x,bound) = (x,) <$> mkBound bound
    mkThing mk   = S.fromList . mconcat <$> sequence [ mk defVars s | (m, s) <- specs, m == name]

mkBound :: (Resolvable a) => Bound (Located BareType) a -> BareM (Bound RSort a)
mkBound (Bound s vs pts xts r)
  = do ptys' <- mapM (\(x, t) -> ((x,) . toRSort . val) <$> mkLSpecType t) pts
       xtys' <- mapM (\(x, t) -> ((x,) . toRSort . val) <$> mkLSpecType t) xts
       vs'   <- map (toRSort . val) <$> mapM mkLSpecType vs
       Bound s vs' ptys' xtys' <$> resolve (loc s) r
