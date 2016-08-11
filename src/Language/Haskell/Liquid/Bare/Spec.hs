{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp  #-}
{-# LANGUAGE TupleSections     #-}

module Language.Haskell.Liquid.Bare.Spec (
    makeClasses
  , makeQualifiers
  , makeHints
  , makeLVar
  , makeLazy
  , makeHMeas, makeHInlines
  , makeTExpr
  , makeTargetVars
  , makeAssertSpec
  , makeAssumeSpec
  , makeDefaultMethods
  , makeIAliases
  , makeInvariants
  , makeNewTypes
  , makeSpecDictionaries
  , makeBounds
  , makeHBounds
  ) where

import           CoreSyn                                    (CoreBind)
import           DataCon
import           MonadUtils                                 (mapMaybeM)
import           Prelude                                    hiding (error)
import           TyCon
import           Var


import           Control.Monad.Except
import           Control.Monad.State
import           Data.Maybe


import qualified Data.List                                  as L
import qualified Data.HashSet                               as S
import qualified Data.HashMap.Strict                        as M



import           Language.Fixpoint.Misc                     (group, snd3, groupList, mapFst)
-- import           Language.Fixpoint.Misc                     (traceShow)


import qualified Language.Fixpoint.Types                    as F
import           Language.Haskell.Liquid.Types.Dictionaries
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.Bounds

import qualified Language.Haskell.Liquid.Measure            as Ms

import           Language.Haskell.Liquid.Bare.Env
import           Language.Haskell.Liquid.Bare.Existential
import           Language.Haskell.Liquid.Bare.Lookup
import           Language.Haskell.Liquid.Bare.Misc          (joinVar)
import           Language.Haskell.Liquid.Bare.OfType
import           Language.Haskell.Liquid.Bare.Resolve
import           Language.Haskell.Liquid.Bare.SymSort
import           Language.Haskell.Liquid.Bare.Measure

makeClasses :: ModName
            -> Config
            -> [Var]
            -> (ModName, Ms.Spec (Located BareType) bndr)
            -> BareM [((DataCon, DataConP), [(ModName, Var, LocSpecType)])]
makeClasses cmod cfg vs (mod, spec) = inModule mod $ mapM mkClass $ Ms.classes spec
  where
    --FIXME: cleanup this code
    unClass = snd . bkClass . fourth4 . bkUniv
    mkClass (RClass cc ss as ms)
            = do let c      = btc_tc cc
                 let l      = loc  c
                 let l'     = locE c
                 tc        <- lookupGhcTyCon c
                 ss'       <- mapM mkLSpecType ss
                 let (dc:_) = tyConDataCons tc
                 let αs  = map bareRTyVar as
                 let as' = [rVar $ symbolTyVar $ F.symbol a | a <- as ]
                 let ms' = [ (s, rFun "" (RApp cc (flip RVar mempty <$> as) [] mempty) <$> t) | (s, t) <- ms]
                 vts <- makeSpec (noCheckUnknown cfg || cmod /= mod) vs ms'
                 let sts = [(val s, unClass $ val t) | (s, _)    <- ms
                                                     | (_, _, t) <- vts]
                 let t   = rCls tc as'
                 let dcp = DataConP l αs [] [] (val <$> ss') (reverse sts) t l'
                 return ((dc,dcp),vts)

makeQualifiers :: (ModName, Ms.Spec ty bndr)
               -> BareM [F.Qualifier]
makeQualifiers (mod,spec) = inModule mod mkQuals
  where
    mkQuals = mapM (\q -> resolve (F.qPos q) q) $ Ms.qualifiers spec

makeHints :: [Var] -> Ms.Spec ty bndr -> BareM [(Var, [Int])]
makeHints   vs spec = varSymbols id vs $ Ms.decr spec

makeLVar :: [Var]
         -> Ms.Spec ty bndr
         -> BareM [Var]
makeLVar    vs spec = fmap fst <$> varSymbols id vs [(v, ()) | v <- Ms.lvars spec]

makeLazy :: [Var]
         -> Ms.Spec ty bndr
         -> BareM [Var]
makeLazy    vs spec = fmap fst <$> varSymbols id vs [(v, ()) | v <- S.toList $ Ms.lazy spec]

makeHBounds :: [Var] -> Ms.Spec ty bndr -> BareM [(Var, LocSymbol)]
makeHBounds vs spec = varSymbols id vs [(v, v ) | v <- S.toList $ Ms.hbounds spec]

makeTExpr :: [Var] -> Ms.Spec ty bndr -> BareM [(Var, [Located F.Expr])]
makeTExpr   vs spec = varSymbols id vs $ Ms.termexprs spec


makeHInlines :: [Var]
             -> Ms.Spec ty bndr
             -> BareM [(Located Var, LocSymbol)]
makeHMeas :: [Var]
           -> Ms.Spec ty bndr
           -> BareM [(Located Var, LocSymbol)]
makeHInlines = makeHIMeas Ms.inlines
makeHMeas    = makeHIMeas Ms.hmeas
makeHIMeas :: (Ms.Spec ty bndr -> S.HashSet LocSymbol)
           -> [Var]
           -> Ms.Spec ty bndr
           -> BareM [(Located Var, LocSymbol)]
makeHIMeas f vs spec
  = fmap tx <$> varSymbols id vs [(v, (loc v, locE v, v)) | v <- S.toList (f spec)]
  where
    tx (x,(l, l', s))  = (Loc l l' x, s)

varSymbols :: ([Var] -> [Var]) -> [Var] -> [(LocSymbol, a)] -> BareM [(Var, a)]
varSymbols f vs  = concatMapM go
  where lvs        = M.map L.sort $ group [(sym v, locVar v) | v <- vs]
        sym        = dropModuleNames . F.symbol . showPpr
        locVar v   = (getSourcePos v, v)
        go (s, ns) = case M.lookup (val s) lvs of
                     Just lvs -> return ((, ns) <$> varsAfter f s lvs)
                     Nothing  -> ((:[]).(,ns)) <$> lookupGhcVar s

varsAfter :: ([b] -> [b]) -> Located a -> [(F.SourcePos, b)] -> [b]
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

grepClassAsserts :: [RInstance t2] -> [(Located F.Symbol, t2)]
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


lookupIds :: GhcLookup a
          => Bool
          -> [(a, t)]
          -> BareM [(Var, a, t)]
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

makeIAliases :: (ModName, Ms.Spec (Located BareType) bndr)
             -> BareM [(Located SpecType, Located SpecType)]
makeIAliases (mod, spec)
  = inModule mod $ makeIAliases' $ Ms.ialiases spec

makeIAliases' :: [(Located BareType, Located BareType)] -> BareM [(Located SpecType, Located SpecType)]
makeIAliases'     = mapM mkIA
  where
    mkIA (t1, t2) = (,) <$> mkI t1 <*> mkI t2
    mkI t         = fmap generalize <$> mkLSpecType t

makeNewTypes :: (ModName, Ms.Spec (Located BareType) bndr)
               -> BareM [(TyCon, Located SpecType)]
makeNewTypes (mod,spec)
  = inModule mod $ makeNewTypes' $ Ms.newtyDecls spec

makeNewTypes' :: [DataDecl] -> BareM [(TyCon, Located SpecType)]
makeNewTypes' = mapM mkNT
  where
    mkNT :: DataDecl -> BareM (TyCon, Located SpecType)
    mkNT d       = (,) <$> (lookupGhcTyCon $ tycName d) 
                       <*> (fmap generalize <$> (getTy (tycSrcPos d) (tycDCons d) >>= mkLSpecType))
    getTy l [(_,[(_,t)])] = return $ withLoc l t 
    getTy l _             = throwError $ ErrOther (sourcePosSrcSpan l) "bad new type declaration"

    withLoc s = Loc s s 


makeInvariants :: (ModName, Ms.Spec (Located BareType) bndr)
               -> BareM [(Maybe Var, Located SpecType)]
makeInvariants (mod,spec)
  = inModule mod $ makeInvariants' $ Ms.invariants spec

makeInvariants' :: [Located BareType] -> BareM [(Maybe Var, Located SpecType)]
makeInvariants' = mapM mkI
  where
    mkI t       = (Nothing,) . fmap generalize <$> mkLSpecType t

makeSpecDictionaries :: F.TCEmb TyCon -> [Var] -> [(a, Ms.BareSpec)] -> GhcSpec
                     -> BareM GhcSpec
makeSpecDictionaries embs vars specs sp
  = do ds <- (dfromList . concat)  <$>  mapM (makeSpecDictionary embs vars) specs
       return $ sp { gsDicts = ds }



makeSpecDictionary :: F.TCEmb TyCon -> [Var] -> (a, Ms.BareSpec)
                   -> BareM [(Var, M.HashMap F.Symbol SpecType)]
makeSpecDictionary embs vars (_, spec)
  = (catMaybes . resolveDictionaries vars) <$> mapM (makeSpecDictionaryOne embs) (Ms.rinstance spec)


makeSpecDictionaryOne :: F.TCEmb TyCon -> RInstance (Located BareType)
                      -> BareM (F.Symbol, M.HashMap F.Symbol SpecType)
makeSpecDictionaryOne embs (RI x t xts)
  = do t'  <- mapM mkLSpecType t
       tyi <- gets tcEnv
       ts' <- map (val . txRefSort tyi embs . fmap txExpToBind) <$> mapM mkTy' ts
       return $ makeDictionary $ RI x (val <$> t') $ zip xs ts'
  where
    mkTy' t  = fmap generalize <$> mkLSpecType t
    (xs, ts) = unzip xts


resolveDictionaries :: [Var] -> [(F.Symbol, M.HashMap F.Symbol SpecType)] -> [Maybe (Var, M.HashMap F.Symbol SpecType)]
resolveDictionaries vars ds  = lookupVar <$> concat (go <$> groupList ds)
 where
    go (x,is)           = addIndex 0 x $ reverse is

    -- GHC internal postfixed same name dictionaries with ints
    addIndex _ _ []     = []
    addIndex _ x [i]    = [(x,i)]
    addIndex j x (i:is) = (F.symbol (F.symbolString x ++ show j),i):addIndex (j+1) x is

    lookupVar (s, i)    = ((,i) <$> lookupName s)
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
