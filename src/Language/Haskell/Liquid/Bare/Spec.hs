{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp  #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE BangPatterns      #-}

module Language.Haskell.Liquid.Bare.Spec (
    makeClasses
  , makeSpecDictionaries

  -- TODO-REBARE , makeQualifiers
  -- TODO-REBARE , makeHints
  -- TODO-REBARE , makeLVar
  -- TODO-REBARE , makeSize
  -- TODO-REBARE , makeLazy
  -- TODO-REBARE , makeAutoInsts
  -- TODO-REBARE , makeDefs
  -- TODO-REBARE , makeHMeas, makeHInlines
  -- TODO-REBARE , makeTExpr
  -- TODO-REBARE , makeIgnoreVars
  -- TODO-REBARE , makeTargetVars
  -- TODO-REBARE , makeAssertSpec
  -- TODO-REBARE , makeAssumeSpec
  -- TODO-REBARE , makeDefaultMethods
  -- TODO-REBARE , makeIAliases
  -- TODO-REBARE , makeInvariants
  -- TODO-REBARE , makeNewTypes
  -- TODO-REBARE , makeBounds
  -- TODO-REBARE , makeHBounds
  -- TODO-REBARE , lookupIds
  ) where

-- import           CoreSyn                                    (CoreBind)
-- import           DataCon
-- import           MonadUtils                                 (mapMaybeM)
-- import           Prelude                                    hiding (error)
-- import           TyCon
-- import           Var

-- import qualified Name 
-- import qualified HscTypes 
-- import qualified OccName as NS

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Bifunctor 
import qualified Data.Maybe                                 as Mb
import qualified Data.List                                  as L
import qualified Data.HashSet                               as S
import qualified Data.HashMap.Strict                        as M

import qualified Language.Fixpoint.Misc                     as Misc
import qualified Language.Fixpoint.Types                    as F
import qualified Language.Fixpoint.Types.Visitor            as F

import           Language.Haskell.Liquid.Types.Dictionaries
import           Language.Haskell.Liquid.GHC.Misc
import qualified Language.Haskell.Liquid.GHC.API            as Ghc
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types              hiding (freeTyVars)
import           Language.Haskell.Liquid.Types.Bounds

import qualified Language.Haskell.Liquid.Measure            as Ms

import           Language.Haskell.Liquid.Bare.Types         as Bare 
import           Language.Haskell.Liquid.Bare.Resolve       as Bare
import           Language.Haskell.Liquid.Bare.Expand        as Bare

-- import           Language.Haskell.Liquid.Bare.OfType        as Bare
-- import           Language.Haskell.Liquid.Bare.Existential
-- import           Language.Haskell.Liquid.Bare.Lookup
-- import           Language.Haskell.Liquid.Bare.Misc          (joinVar)
-- import           Language.Haskell.Liquid.Bare.SymSort
-- import           Language.Haskell.Liquid.Bare.Measure

-------------------------------------------------------------------------------
makeClasses :: Bare.Env -> Bare.SigEnv -> ModName -> Bare.ModSpecs 
            -> ([DataConP], [(ModName, Ghc.Var, LocSpecType)])
-------------------------------------------------------------------------------
makeClasses env sigEnv myName specs = -- (mempty, mempty) -- TODO-REBARE  
  second mconcat . unzip 
  $ [ mkClass env sigEnv myName name cls tc
        | (name, spec) <- M.toList specs
        , cls          <- Ms.classes spec
        , tc           <- Mb.maybeToList (classTc cls) 
    ]
  where
    classTc = Bare.maybeResolveSym env myName "makeClass" . btc_tc . rcName 

mkClass :: Bare.Env -> Bare.SigEnv -> ModName -> ModName -> RClass LocBareType -> Ghc.TyCon 
        -> (DataConP, [(ModName, Ghc.Var, LocSpecType)])
mkClass env sigEnv myName name (RClass cc ss as ms) tc = F.notracepp msg (dcp, vts)
  where
    dcp    = DataConP l dc αs [] [] (val <$> ss') (reverse sts) t False (F.symbol name) l'
    c      = btc_tc cc
    l      = loc  c
    l'     = locE c
    ss'    = mkConstr env sigEnv name <$> ss 
    msg    = "MKCLASS: " ++ F.showpp (cc, as, αs) -- , as')
    (dc:_) = Ghc.tyConDataCons tc
    αs     = bareRTyVar <$> as
    as'    = [rVar $ symbolTyVar $ F.symbol a | a <- as ]
    ms'    = [ (s, rFun "" (RApp cc (flip RVar mempty <$> as) [] mempty) <$> t) | (s, t) <- ms]
    vts    = makeMethod env sigEnv name <$> ms'
    sts    = F.notracepp "METHODS" $
             [(val s, unClass $ val t) 
                | (s, _)    <- ms
                | (_, _, t) <- vts]
    t      = rCls tc as'

mkConstr :: Bare.Env -> Bare.SigEnv -> ModName -> LocBareType -> LocSpecType     
mkConstr env sigEnv name = fmap dropUniv . Bare.cookSpecType env sigEnv name Nothing
  where 
    dropUniv t           = t' where (_, _, _, t') = bkUniv t

   --FIXME: cleanup this code
unClass :: SpecType -> SpecType 
unClass = snd . bkClass . fourth4 . bkUniv

-- formerly, makeSpec
makeMethod :: Bare.Env -> Bare.SigEnv -> ModName -> (LocSymbol, LocBareType) 
         -> (ModName, Ghc.Var, LocSpecType)
makeMethod env sigEnv name (lx, bt) = (name, v, t) 
  where 
    v = Bare.lookupGhcVar env        name "makeMethod" lx
    t = F.notracepp msg $ Bare.cookSpecType env sigEnv name (Just v)   bt 
    msg = "MAKE-SPEC: " ++ F.showpp lx 


-------------------------------------------------------------------------------
makeSpecDictionaries :: Bare.Env -> Bare.SigEnv -> ModSpecs -> DEnv Ghc.Var SpecType 
-------------------------------------------------------------------------------
makeSpecDictionaries env sigEnv specs
  = dfromList 
  . concat 
  . fmap (makeSpecDictionary env sigEnv) 
  $ M.toList specs

makeSpecDictionary :: Bare.Env -> Bare.SigEnv -> (ModName, Ms.BareSpec)
                   -> [(Ghc.Var, M.HashMap F.Symbol (RISig SpecType))]
makeSpecDictionary env sigEnv (name, spec)
  = Mb.catMaybes 
  . resolveDictionaries env name 
  . fmap (makeSpecDictionaryOne env sigEnv name) 
  . Ms.rinstance 
  $ spec

makeSpecDictionaryOne :: Bare.Env -> Bare.SigEnv -> ModName 
                      -> RInstance LocBareType 
                      -> (F.Symbol, M.HashMap F.Symbol (RISig SpecType))
makeSpecDictionaryOne env sigEnv name (RI x t xts)
         = makeDictionary $ RI x (val . mkTy <$> t) [(x, mkLSpecIType t) | (x, t) <- xts ] 
  where
    mkTy :: LocBareType -> LocSpecType
    mkTy = Bare.cookSpecType env sigEnv name Nothing 

    mkLSpecIType :: RISig LocBareType -> RISig SpecType
    mkLSpecIType = fmap (val . mkTy)

resolveDictionaries :: Bare.Env -> ModName -> [(F.Symbol, M.HashMap F.Symbol (RISig SpecType))] 
                    -> [Maybe (Ghc.Var, M.HashMap F.Symbol (RISig SpecType))]
resolveDictionaries env name = fmap lookupVar 
                             . concat 
                             . fmap addInstIndex 
                             . Misc.groupList 
  where
    lookupVar (x, inst)      = (, inst) <$> Bare.maybeResolveSym env name "resolveDict" (F.dummyLoc x)

    -- REBARE lookupVar (x, inst) = (, inst) <$> lookupName x
    -- REBARE: lookupName x        = case filter ((== x) . fst) ((\v -> (dropModuleNames $ F.symbol $ show v, v)) <$> vars) of
                            -- REBARE: [(_, v)] -> Just v
                            -- REBARE: _        -> Nothing
                            -- REBARE: vars --> shortSymbol

-- formerly, addIndex
-- GHC internal postfixed same name dictionaries with ints
addInstIndex            :: (F.Symbol, [a]) -> [(F.Symbol, a)]
addInstIndex (x, is) = go 0 (reverse is)
  where 
    go _ []          = []
    go _ [i]         = [(x, i)]
    go j (i:is)      = (F.symbol (F.symbolString x ++ show j),i) : go (j+1) is



{- 
lookupIds :: Bool -> [(LocSymbol, a)] -> BareM [(Var, LocSymbol, a)]
lookupIds !ignoreUnknown
  = mapMaybeM lookup
  where
    lookup (s, t)
      | isWorker (val s)
      = (Just . (,s,t) <$> lookupGhcWrkVar s) `catchError` handleError
      | otherwise
      = (Just . (,s,t) <$> lookupGhcVar    s) `catchError` handleError
    handleError ( ErrGhc {})
      | ignoreUnknown
      = return Nothing
    handleError err
      = throwError err

mkVarSpec :: (Var, LocSymbol, LocBareType) -> BareM (Var, LocSpecType)
mkVarSpec (v, _, b) = (v,) . fmap (txCoerce . generalize) <$> mkLSpecType b
  where
    coSub           = M.fromList [ (F.symbol a, F.FObj (specTvSymbol a)) | a <- tvs ]
    tvs             = bareTypeVars (val b)
    specTvSymbol    = F.symbol . bareRTyVar
    txCoerce        = mapExprReft (\_ -> F.applyCoSub coSub)


bareTypeVars :: BareType -> [BTyVar]
bareTypeVars t = Misc.sortNub . fmap ty_var_value $ vs ++ vs'
  where
    vs         = fst4 . bkUniv $ t
    vs'        = freeTyVars    $ t

-}

{- TODO-REBARE 

makeQualifiers :: (ModName, Ms.Spec ty bndr) -> BareM [F.Qualifier]
makeQualifiers (mod,spec) = inModule mod mkQuals
  where
    mkQuals = mapM (\q -> resolve (F.qPos q) q) $ Ms.qualifiers spec

makeHints :: [Var] -> Ms.Spec ty bndr -> BareM [(Var, [Int])]
makeHints   vs spec = varSymbols id vs $ Ms.decr spec

makeLVar :: [Var] -> Ms.Spec ty bndr -> BareM [Var]
makeLVar vs spec = fmap fst <$> varSymbols id vs [(v, ()) | v <- Ms.lvars spec]

makeSize :: [Var] -> Ms.Spec ty bndr -> BareM [Var]
makeSize    vs spec = fmap fst <$> varSymbols id vs [(v, ()) | v <-  lzs]
  where
    lzs = catMaybes (getSizeFuns <$> Ms.dataDecls spec)
    getSizeFuns decl
      | Just x       <- tycSFun decl
      , SymSizeFun f <- x
      = Just f
      | otherwise
      = Nothing

makeLazy :: [Var]
         -> Ms.Spec ty bndr
         -> BareM [Var]
makeLazy    vs spec = fmap fst <$> varSymbols id vs [(v, ()) | v <-  S.toList (Ms.lazy spec)]

makeAutoInsts :: [Var]
              -> Ms.Spec ty bndr
              -> BareM [(Var, Maybe Int)]
makeAutoInsts vs spec = varSymbols id vs (M.toList $ Ms.autois spec)

makeDefs :: [Var] -> Ms.Spec ty bndr -> BareM [(Var, F.Symbol)]
makeDefs vs spec = varSymbols id vs (M.toList $ Ms.defs spec)

makeHBounds :: [Var] -> Ms.Spec ty bndr -> BareM [(Var, LocSymbol)]
makeHBounds vs spec = varSymbols id vs [(v, v ) | v <- S.toList $ Ms.hbounds spec]

makeTExpr :: [Var] -> Ms.Spec ty bndr -> BareM [(Var, [Located F.Expr])]
makeTExpr   vs spec = varSymbols id vs $ Ms.termexprs spec

makeHInlines :: [Var] -> Ms.Spec ty bndr -> BareM [(Located Var, LocSymbol)]
makeHInlines = makeHIMeas Ms.inlines

makeHMeas :: [Var] -> Ms.Spec ty bndr -> BareM [(Located Var, LocSymbol)]
makeHMeas = makeHIMeas Ms.hmeas

makeHIMeas :: (Ms.Spec ty bndr -> S.HashSet LocSymbol)
           -> [Var]
           -> Ms.Spec ty bndr
           -> BareM [(Located Var, LocSymbol)]
makeHIMeas f vs spec
  = fmap tx <$> varSymbols id vs [(v, (loc v, locE v, v)) | v <- S.toList (f spec)]
  where
    tx (x, (l, l', s))  = (Loc l l' x, s)

varSymbols :: ([Var] -> [Var]) -> [Var] -> [(LocSymbol, a)] -> BareM [(Var, a)]
varSymbols f vs = concatMapM go
  where
    lvs         = M.map L.sort $ Misc.group [(sym v, locVar v) | v <- vs]
    sym         = dropModuleNames . F.symbol . showPpr
    locVar v    = (getSourcePos v, v)
    go (s, ns)  = case M.lookup (val s) lvs of
                    Just lvs -> return  ((, ns) <$> varsAfter f s lvs)
                    Nothing  -> ((:[]) . (,ns)) <$> lookupGhcVar s

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


--------------------------------------------------------------------------------
-- | API: Bare Refinement Types ------------------------------------------------
--------------------------------------------------------------------------------
makeIgnoreVars :: ModName -> [Var] -> S.HashSet LocSymbol -> BareM [Var]
makeIgnoreVars name vars ignores = do 
  env         <- gets hscEnv 
  ignoreNames <- mkNames env name (S.toList ignores)
  return        [ v | v <- vars, varName v `elem` ignoreNames ] 

makeTargetVars :: ModName -> [Var] -> [String] -> BareM [Var]
makeTargetVars name vars checkVars = do 
  env          <- gets hscEnv
  checkNames   <- mkNames env name (dummyLoc . prefix <$> checkVars)
  return        [ v | v <- vars, varName v `elem` checkNames ] 
  where
    prefix s    = qualifySymbol (F.symbol name) (F.symbol s)
    
mkNames :: HscTypes.HscEnv -> ModName -> [LocSymbol] -> BareM [Name.Name]
mkNames env name = liftIO . concatMapM (lookupName env name (Just NS.varName))

makeAssertSpec :: ModName -> Config -> [Var] -> [Var] -> (ModName, Ms.BareSpec)
               -> BareM [(ModName, Var, LocSpecType)]
makeAssertSpec cmod cfg vs lvs (mod, spec)
  | cmod == mod
  = makeLocalSpec cfg cmod vs lvs (grepClassAsserts (Ms.rinstance spec)) (Ms.sigs spec ++ Ms.localSigs spec)
  | otherwise
  = inModule mod $ makeSpec True vs $ Ms.sigs spec

makeAssumeSpec
  :: ModName -> Config -> [Var] -> [Var] -> (ModName, Ms.BareSpec)
  -> BareM [(ModName, Var, LocSpecType)]
makeAssumeSpec cmod cfg vs lvs (mod, spec)
  | cmod == mod
  = makeLocalSpec cfg cmod vs lvs (grepClassAssumes (Ms.rinstance spec)) $ Ms.asmSigs spec
  | otherwise
  = inModule mod $ makeSpec True vs $  Ms.asmSigs spec

grepClassAsserts :: [RInstance t] -> [(Located F.Symbol, t)]
grepClassAsserts           = concatMap go
   where
    go    xts              = mapMaybe goOne (risigs xts)
    goOne (x, RISig t)     = Just ((F.symbol . (".$c" ++ ) . F.symbolString) <$> x, t)
    goOne (_, RIAssumed _) = Nothing

grepClassAssumes :: [RInstance t] -> [(Located F.Symbol, t)]
grepClassAssumes  = concatMap go
   where
    go    xts              = catMaybes $ map goOne $ risigs xts
    goOne (x, RIAssumed t) = Just (fmap (F.symbol . (".$c" ++ ) . F.symbolString) x, t)
    goOne (_, RISig _)     = Nothing

makeDefaultMethods :: [Var] -> [(ModName, Var, Located SpecType)] -> [(ModName, Var, Located SpecType)]
makeDefaultMethods defVs sigs
  = [ (m,dmv,t)
    | dmv <- defVs
    , let dm = F.symbol $ showPpr dmv
    , "$dm" `F.isPrefixOfSym` dropModuleNames dm
    , let mod    = takeModuleNames dm
    , let method = qualifySymbol mod $ F.dropSym 3 (dropModuleNames dm)
    , let mb     = L.find ((method `F.isPrefixOfSym`) . F.symbol . Misc.snd3) sigs
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
       return $ (vts1 ++ vts2)
  where
    xbs1                = xbs1' ++ cbs
    (xbs1', xbs2)       = L.partition (modElem mod . fst) xbs
    dupSnd (x, y)       = (dropMod x, (x, y))
    expand3 (x, (y, w)) = (x, y, w)
    dropMod             = fmap (dropModuleNames . F.symbol)
    fchoose ls          = maybe ls (:[]) $ L.find (`elem` vs) ls
    modElem n x         = takeModuleNames (val x) == F.symbol n



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
    mkNT d       = (,) <$> lookupGhcTyCon "makeNewTypes'" (tycName d)
                       <*> (fmap generalize <$> (getTy (tycSrcPos d) (tycDCons d) >>= mkLSpecType))

    getTy l [c]
      | [(_, t)] <- dcFields c = return $ withLoc l t
    getTy l _                  = throwError $ ErrOther (sourcePosSrcSpan l) "bad new type declaration"
    -- getTy l [(_,[(_,t)])] = return $ withLoc l t

    withLoc s = Loc s s


makeInvariants :: (ModName, Ms.Spec (Located BareType) bndr)
               -> BareM [(Maybe Var, Located SpecType)]
makeInvariants (mod,spec)
  = inModule mod $ makeInvariants' $ Ms.invariants spec

makeInvariants' :: [(a, Located BareType)] -> BareM [(Maybe Var, Located SpecType)]
makeInvariants' = mapM mkI
  where
    mkI (_,t)       = (Nothing,) . fmap generalize <$> mkLSpecType t



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

-}