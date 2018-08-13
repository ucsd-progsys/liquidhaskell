-- | This module has the code that uses the GHC definitions to:
--   1. MAKE a name-resolution environment,
--   2. USE the environment to translate plain symbols into Var, TyCon, etc. 

{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TupleSections         #-}

module Language.Haskell.Liquid.Bare.Resolve 
  ( -- * Creating the Environment
    makeEnv 

    -- * Resolving symbols 
  , ResolveSym (..)
  , Qualify (..)
  
  -- * Looking up names
  -- , strictResolveSym
  , maybeResolveSym 
  , lookupGhcDataCon 
  , lookupGhcDnTyCon 
  , lookupGhcTyCon 
  , lookupGhcVar 
  , lookupGhcNamedVar 

  -- * Checking if names exist
  , knownGhcVar 
  , knownGhcTyCon 
  , knownGhcDataCon 
  , knownGhcType 

  -- * Misc 
  , srcVars 

  -- * Conversions from Bare
  , ofBareTypeE
  , ofBareType
  , ofBPVar
  , mkSpecType'
  -- , ofBareExpr

  -- * Post-processing types
  , txRefSort
  ) where 

import qualified Control.Exception as Ex 
import qualified Data.List                         as L 
import qualified Data.HashSet                      as S 
import qualified Data.Maybe                        as Mb
import qualified Data.HashMap.Strict               as M
import qualified Text.PrettyPrint.HughesPJ         as PJ 

import qualified Language.Fixpoint.Types               as F 
import qualified Language.Fixpoint.Misc                as Misc 

import qualified Language.Haskell.Liquid.GHC.API       as Ghc 
import qualified Language.Haskell.Liquid.GHC.Misc      as GM 
import qualified Language.Haskell.Liquid.Misc          as Misc 
import qualified Language.Haskell.Liquid.Types.RefType as RT
import           Language.Haskell.Liquid.Types.Types   
import           Language.Haskell.Liquid.Types.Specs 
import           Language.Haskell.Liquid.Bare.Types 
import           Language.Haskell.Liquid.Bare.Misc   
import           Language.Haskell.Liquid.WiredIn 

-------------------------------------------------------------------------------
-- | Creating an environment 
-------------------------------------------------------------------------------
makeEnv :: Config -> GhcSrc -> LogicMap -> Env 
makeEnv cfg src lmap = RE 
  { reLMap      = lmap
  , reSyms      = syms 
  , _reSubst    = makeVarSubst   src 
  , _reTyThings = makeTyThingMap src 
  , reCfg       = cfg
  , reQImps     = gsQImports     src
  , reLocalVars = F.tracepp "LocalVars" $ makeLocalVars src 
  } 
  where 
    syms        = [ (F.symbol v, v) | v <- vars ] 
    vars        = srcVars src

makeLocalVars :: GhcSrc -> LocalVars 
makeLocalVars = localVarMap . localBinds . giCbs

localBinds :: [Ghc.CoreBind] -> [Ghc.Var]
localBinds                    = concatMap (bgo S.empty) 
  where
    add  x g                  = maybe g (`S.insert` g) (localKey x) 
    adds b g                  = foldr add g (Ghc.bindersOf b) 
    take x g                  = maybe [] (\k -> if S.member k g then [] else [x]) (localKey x)
    pgo g (x, e)              = take x g ++ go (add x g) e
    bgo g (Ghc.NonRec x e)    = pgo g (x, e) 
    bgo g (Ghc.Rec xes)       = concatMap (pgo g) xes 
    go  g (Ghc.App e a)       = concatMap (go  g) [e, a]
    go  g (Ghc.Lam x e)       = go g e
    go  g (Ghc.Let b e)       = bgo g b ++ go (adds b g) e 
    go  g (Ghc.Tick _ e)      = go g e
    go  g (Ghc.Cast e _)      = go g e
    go  g (Ghc.Case e x _ cs) = go g e ++ concatMap (go g . Misc.thd3) cs
    go  g (Ghc.Var _)         = []
    go  _ _                   = []

localVarMap :: [Ghc.Var] -> LocalVars
localVarMap vs = 
  Misc.group [ (x, (i, v)) | v    <- vs
                           , x    <- Mb.maybeToList (localKey v) 
                           , let i = F.srcLine v 
             ]

localKey   :: Ghc.Var -> Maybe F.Symbol
localKey v 
  | isLocal m = Just x 
  | otherwise = Nothing
  where 
    (m, x)    = splitModuleNameExact . GM.dropModuleUnique . F.symbol $ v 

makeVarSubst :: GhcSrc -> F.Subst 
makeVarSubst src = F.mkSubst unqualSyms 
  where 
    unqualSyms   = [ (x, mkVarExpr v) 
                       | (x, mxs) <- M.toList       (makeSymMap src) 
                       , v        <- Mb.maybeToList (okUnqualified me mxs) 
                       , not (isWiredInName x)
                   ] 
    me           = F.symbol (giTargetMod src) 

-- | @okUnqualified mod mxs@ takes @mxs@ which is a list of modulenames-var 
--   pairs all of which have the same unqualified symbol representation. 
--   The function returns @Just v@ if 
--   1. that list is a singleton i.e. there is a UNIQUE unqualified version, OR
--   2. there is a version whose module equals @me@.

okUnqualified :: F.Symbol -> [(F.Symbol, a)] -> Maybe a 
okUnqualified _ [(_, x)] = Just x 
okUnqualified me mxs     = go mxs 
  where 
    go []                = Nothing 
    go ((m,x) : rest)    
      | me == m          = Just x 
      | otherwise        = go rest 


makeSymMap :: GhcSrc -> M.HashMap F.Symbol [(F.Symbol, Ghc.Var)]
makeSymMap src = Misc.group [ (sym, (m, x)) 
                                | x           <- srcVars src
                                , let (m, sym) = qualifiedSymbol x ]

makeTyThingMap :: GhcSrc -> TyThingMap 
makeTyThingMap src = 
  -- F.tracepp "makeTyThingMap" $ 
  Misc.group [ (x, (m, t))  | t         <- srcThings src
                            , let (m, x) = qualifiedSymbol t 
                            , not (isLocal m)
             ] 

isLocal :: F.Symbol -> Bool
isLocal = isEmptySymbol 

qualifiedSymbol :: (F.Symbolic a) => a -> (F.Symbol, F.Symbol)
qualifiedSymbol = splitModuleNameExact . F.symbol 

-- qualifiedSymbol (Ghc.AnId x) = splitModuleNameExact . GM.dropModuleUnique . F.symbol $ x  

-- dropLocalUnique :: (F.Symbol, F.Symbol) -> (F.Symbol, F.Symbol)
-- dropLocalUnique (m, x)      
--   | otherwise  = (m, x) 

isEmptySymbol :: F.Symbol -> Bool 
isEmptySymbol x = F.lengthSym x == 0 

srcThings :: GhcSrc -> [Ghc.TyThing] 
srcThings src = Misc.hashNubWith F.showpp (gsTyThings src ++ mySrcThings src) 

mySrcThings :: GhcSrc -> [Ghc.TyThing] 
mySrcThings src = [ Ghc.AnId   x | x <- vars ] 
               ++ [ Ghc.ATyCon c | c <- tcs  ] 
               ++ [ aDataCon   d | d <- dcs  ] 
  where 
    vars        = Misc.sortNub $ dataConVars dcs ++ srcVars  src
    dcs         = Misc.sortNub $ concatMap Ghc.tyConDataCons tcs 
    tcs         = Misc.sortNub $ srcTyCons src  
    aDataCon    = Ghc.AConLike . Ghc.RealDataCon 

srcTyCons :: GhcSrc -> [Ghc.TyCon]
srcTyCons src = concat 
  [ gsTcs     src 
  , gsFiTcs   src 
  , gsPrimTcs src
  , srcVarTcs src 
  ]

srcVarTcs :: GhcSrc -> [Ghc.TyCon]
srcVarTcs = varTyCons . srcVars 

varTyCons :: [Ghc.Var] -> [Ghc.TyCon]
varTyCons = concatMap (typeTyCons . Ghc.dropForAlls . Ghc.varType) 

typeTyCons :: Ghc.Type -> [Ghc.TyCon]
typeTyCons t = tops t ++ inners t 
  where 
    tops     = Mb.maybeToList . Ghc.tyConAppTyCon_maybe
    inners   = concatMap typeTyCons . snd . Ghc.splitAppTys 

-- tyConAppTyCon_maybe :: Type -> Maybe TyCon 
-- splitAppTys :: Type -> (Type, [Type]) 

srcVars :: GhcSrc -> [Ghc.Var]
srcVars src = Misc.sortNub . filter Ghc.isId $ concat 
  [ giDerVars src
  , giImpVars src 
  , giDefVars src 
  , giUseVars src 
  , [ x | Ghc.AnId x <- gsTyThings src ]
  ]

dataConVars :: [Ghc.DataCon] -> [Ghc.Var]
dataConVars dcs = concat 
  [ Ghc.dataConWorkId <$> dcs 
  , Ghc.dataConWrapId <$> dcs 
  ] 
-------------------------------------------------------------------------------
-- | Qualify various names 
-------------------------------------------------------------------------------
class Qualify a where 
  qualify :: Env -> ModName -> a -> a 

instance Qualify TyConP where 
  qualify env name tcp = tcp { tcpSizeFun = qualify env name <$> tcpSizeFun tcp }

instance Qualify SizeFun where 
  qualify env name (SymSizeFun lx) = SymSizeFun (qualify env name lx)
  qualify _   _    sf              = sf

instance Qualify F.Equation where 
  qualify _env _name x = x -- TODO-REBARE 
-- REBARE: qualifyAxiomEq :: Bare.Env -> Var -> Subst -> AxiomEq -> AxiomEq
-- REBARE: qualifyAxiomEq v su eq = subst su eq { eqName = symbol v}

instance Qualify F.Symbol where 
  qualify = qualifySymbol 

qualifySymbol :: Env -> ModName -> F.Symbol -> F.Symbol                                                   
qualifySymbol env name x
  | isWiredInName x = x 
  | otherwise       = case resolveSym env name "Symbol" x of 
                        Left  _ -> x 
                        Right v -> v 

-- REBARE: qualifySymbol :: Env -> F.Symbol -> F.Symbol
-- REBARE: qualifySymbol env x = maybe x F.symbol (M.lookup x syms)


instance (Qualify a) => Qualify (Located a) where 
  qualify env name = fmap (qualify env name) 

instance Qualify SpecType where 
  qualify = substEnv 

instance Qualify F.Expr where 
  qualify = substEnv 

instance Qualify Body where 
  qualify env name (P   p) = P   (qualify env name p) 
  qualify env name (E   e) = E   (qualify env name e)
  qualify env name (R x p) = R x (qualify env name p)

instance Qualify RReft where 
  qualify = substEnv 

instance Qualify F.Qualifier where 
  qualify = substEnv 


instance Qualify TyConInfo where 
  qualify env name tci = tci { sizeFunction = qualify env name <$> sizeFunction tci }

instance Qualify RTyCon where 
  qualify env name rtc = rtc { rtc_info = qualify env name $ rtc_info rtc }

instance Qualify (Measure SpecType Ghc.DataCon) where 
  qualify env name m = substEnv env name $ m { msName = qualify env name (msName m)}

substEnv :: (F.Subable a) => Env -> ModName -> a -> a 
substEnv env name = F.substa (qualifySymbol env name) 
-- substEnv env _ = F.subst (_reSubst env)

-------------------------------------------------------------------------------
lookupGhcNamedVar :: (Ghc.NamedThing a, F.Symbolic a) => Env -> ModName -> a -> Ghc.Var
-------------------------------------------------------------------------------
lookupGhcNamedVar env name z = strictResolveSym env name "Var" lx 
  where 
    lx                       = GM.namedLocSymbol z

lookupGhcVar :: Env -> ModName -> String -> LocSymbol -> Ghc.Var 
lookupGhcVar env name kind lx = 
  case resolveLocSym env name kind lx of 
    Right v -> v 
    Left  e -> case lookupLocalVar env lx of 
                 Just v  -> v 
                 Nothing -> Misc.errorP "error-lookupGhcVar" (F.showpp e)

lookupLocalVar :: Env -> LocSymbol -> Maybe Ghc.Var
lookupLocalVar env lx = Misc.findNearest (F.srcLine lx) kvs
  where 
    kvs               = M.lookupDefault [] x (reLocalVars env) 
    xn                = F.srcLine lx  
    (_, x)            = unQualifySymbol (F.val lx)


lookupGhcDataCon :: Env -> ModName -> String -> LocSymbol -> Ghc.DataCon 
lookupGhcDataCon = strictResolveSym 

lookupGhcTyCon :: Env -> ModName -> String -> LocSymbol -> Ghc.TyCon 
lookupGhcTyCon = strictResolveSym 

lookupGhcDnTyCon :: Env -> ModName -> String -> DataName -> Ghc.TyCon
lookupGhcDnTyCon env name msg (DnCon  s) = lookupGhcDnCon env name msg s
lookupGhcDnTyCon env name msg (DnName s) = Mb.fromMaybe dnc (maybeResolveSym env name msg s) 
  where 
    dnc                                  = lookupGhcDnTyCon env name msg (DnCon s) 

lookupGhcDnCon :: Env -> ModName -> String -> LocSymbol -> Ghc.TyCon 
lookupGhcDnCon env name msg = Ghc.dataConTyCon . lookupGhcDataCon env name msg

-------------------------------------------------------------------------------
-- | Checking existence of names 
-------------------------------------------------------------------------------
knownGhcType :: Env ->  ModName -> LocBareType -> Bool
knownGhcType env name (F.Loc l _ t) = -- F.tracepp ("knownType: " ++ F.showpp t) $
  case ofBareTypeE env name l t of 
    Left e  -> F.tracepp ("knownType: " ++ F.showpp (t, e)) $ False 
    Right _ -> True 

--   where 
--    tcs                  = F.tracepp ("TYCONS: " ++ F.showpp t) $ rTypeTyCons t 
--    t                    = val lt
--    knownBtc             = knownGhcTyCon env name . btc_tc

rTypeTyCons :: (Ord c) => RType c tv r -> [c]
rTypeTyCons           = Misc.sortNub . foldRType f []   
  where 
    f acc t@(RApp {}) = rt_tycon t : acc 
    f acc _           = acc


knownGhcVar :: Env -> ModName -> LocSymbol -> Bool 
knownGhcVar env name lx = Mb.isJust v 
  where 
    v :: Maybe Ghc.Var 
    v = F.notracepp ("knownGhcVar " ++ F.showpp lx) 
      $ maybeResolveSym env name "known-var" lx 

knownGhcTyCon :: Env -> ModName -> LocSymbol -> Bool 
knownGhcTyCon env name lx = Mb.isJust v 
  where 
    v :: Maybe Ghc.TyCon 
    v = maybeResolveSym env name "known-tycon" lx 

knownGhcDataCon :: Env -> ModName -> LocSymbol -> Bool 
knownGhcDataCon env name lx = Mb.isJust v 
  where 
    v :: Maybe Ghc.TyCon 
    v = maybeResolveSym env name "known-var" lx 







-------------------------------------------------------------------------------
-- | Using the environment 
-------------------------------------------------------------------------------
class ResolveSym a where 
  resolveLocSym :: Env -> ModName -> String -> LocSymbol -> Either UserError a 
  
instance ResolveSym Ghc.Var where 
  resolveLocSym = resolveWith $ \case {Ghc.AnId x -> Just x; _ -> Nothing}

instance ResolveSym Ghc.TyCon where 
  resolveLocSym = resolveWith $ \case {Ghc.ATyCon x -> Just x; _ -> Nothing}

instance ResolveSym Ghc.DataCon where 
  resolveLocSym = resolveWith $ \case {Ghc.AConLike (Ghc.RealDataCon x) -> Just x; _ -> Nothing}

instance ResolveSym F.Symbol where 
  resolveLocSym env name _ lx = case resolveLocSym env name "Var" lx of 
    Left _               -> Right (val lx)
    Right (v :: Ghc.Var) -> Right (F.symbol v)


resolveWith :: (Ghc.TyThing -> Maybe a) -> Env -> ModName -> String -> LocSymbol 
            -> Either UserError a 
resolveWith f env name kind lx = 
  case Mb.mapMaybe f things of 
    []  -> Left  (errResolve kind lx) 
    x:_ -> Right x 
  where 
    things = lookupTyThing env name (val lx) 

-------------------------------------------------------------------------------
-- | @lookupTyThing@ is the central place where we lookup the @Env@ to find 
--   any @Ghc.TyThing@ that match that name.  
-------------------------------------------------------------------------------
lookupTyThing :: Env -> ModName -> F.Symbol -> [Ghc.TyThing]
-------------------------------------------------------------------------------
lookupTyThing env name sym = [ t | (m, t) <- things, matchMod m mods] 
  where 
    things                 = M.lookupDefault [] x (_reTyThings env)
    (x, mods)              = symbolModules env sym
    matchMod m Nothing     = True 
    matchMod m (Just ms)   
      | isEmptySymbol m    = ms == [F.symbol name]        -- local variable, see tests-names-pos-local00.hs
      | otherwise          = any (`F.isPrefixOfSym` m) ms -- to allow matching re-exported names e.g. Data.Set.union for Data.Set.Internal.union
                             -- m `elem` ms
                             
symbolModules :: Env -> F.Symbol -> (F.Symbol, Maybe [F.Symbol])
symbolModules env s = (x, glerb <$> modMb) 
  where 
    (modMb, x)      = unQualifySymbol s 
    glerb m         = M.lookupDefault [m] m (reQImps env) 
 
-- | `unQualifySymbol name sym` splits `sym` into a pair `(mod, rest)` where 
--   `mod` is the name of the module, derived from `sym` if qualified.
unQualifySymbol :: F.Symbol -> (Maybe F.Symbol, F.Symbol)
unQualifySymbol sym 
  | GM.isQualifiedSym sym = Misc.mapFst Just (splitModuleNameExact sym) 
  | otherwise             = (Nothing, sym) 

splitModuleNameExact :: F.Symbol -> (F.Symbol, F.Symbol)
splitModuleNameExact x = (GM.takeModuleNames x, GM.dropModuleNames x)

-- srcDataCons :: GhcSrc -> [Ghc.DataCon]
-- srcDataCons src = concatMap Ghc.tyConDataCons (srcTyCons src) 

{- 
  let expSyms     = S.toList (exportedSymbols mySpec)
  syms0 <- liftedVarMap (varInModule name) expSyms
  syms1 <- symbolVarMap (varInModule name) vars (S.toList $ importedSymbols name   specs)
  syms2    <- symbolVarMap (varInModule name) (vars ++ map fst cs') fSyms
  let fSyms =  freeSymbols xs' (sigs ++ asms ++ cs') ms' ((snd <$> invs) ++ (snd <$> ialias))
            ++ measureSymbols measures
   * Symbol :-> [(ModuleName, TyCon)]
   * Symbol :-> [(ModuleName, Var  )]
   * 
 -}   


errResolve :: String -> LocSymbol -> UserError 
errResolve kind lx =  ErrResolve (GM.fSrcSpan lx) (PJ.text msg)
  where 
    msg            = unwords [ "Name resolution error: ", kind, symbolicIdent lx]

symbolicIdent :: (F.Symbolic a) => a -> String
symbolicIdent x = "'" ++ symbolicString x ++ "'"

symbolicString :: F.Symbolic a => a -> String
symbolicString = F.symbolString . F.symbol

resolveSym :: (ResolveSym a) => Env -> ModName -> String -> F.Symbol -> Either UserError a 
resolveSym env name kind x = resolveLocSym env name kind (F.dummyLoc x) 

-- | @strictResolve@ wraps the plain @resolve@ to throw an error 
--   if the name being searched for is unknown.
strictResolveSym :: (ResolveSym a) => Env -> ModName -> String -> LocSymbol -> a 
strictResolveSym env name kind x = case resolveLocSym env name kind x of 
  Left  err -> Misc.errorP "error-strictResolveSym" (F.showpp err) -- uError err 
  Right val -> val 

-- | @maybeResolve@ wraps the plain @resolve@ to return @Nothing@ 
--   if the name being searched for is unknown.
maybeResolveSym :: (ResolveSym a) => Env -> ModName -> String -> LocSymbol -> Maybe a 
maybeResolveSym env name kind x = case resolveLocSym env name kind x of 
  Left  _   -> Nothing 
  Right val -> Just val 
  
------ JUNK-- USE "QUALIFY"class Resolvable a where 
  ------ JUNK-- USE "QUALIFY"resolve :: Env -> ModName -> F.SourcePos -> a -> a  
------ JUNK-- USE "QUALIFY"
------ JUNK-- USE "QUALIFY"instance Resolvable F.Qualifier where 
  ------ JUNK-- USE "QUALIFY"resolve _ _ _ q = q -- TODO-REBARE 
------ JUNK-- USE "QUALIFY"
------ JUNK-- USE "QUALIFY"instance Resolvable RReft where 
  ------ JUNK-- USE "QUALIFY"resolve _ _ _ r = r -- TODO-REBARE 
------ JUNK-- USE "QUALIFY"
------ JUNK-- USE "QUALIFY"instance Resolvable F.Expr where 
  ------ JUNK-- USE "QUALIFY"resolve _ _ _ e = e -- TODO-REBARE 
  ------ JUNK-- USE "QUALIFY"
------ JUNK-- USE "QUALIFY"instance Resolvable a => Resolvable (Located a) where 
  ------ JUNK-- USE "QUALIFY"resolve env name _ lx = F.atLoc lx (resolve env name (F.loc lx) (val lx))

-------------------------------------------------------------------------------
-- | HERE 
-------------------------------------------------------------------------------

ofBareType :: Env -> ModName -> F.SourcePos -> BareType -> SpecType 
ofBareType env name l t = either (Misc.errorP "error-ofBareType" . F.showpp) id (ofBareTypeE env name l t)

ofBareTypeE :: Env -> ModName -> F.SourcePos -> BareType -> Either UserError SpecType 
ofBareTypeE env name l t = ofBRType env name (qualify env name) l t 

ofBSort :: Env -> ModName -> F.SourcePos -> BSort -> RSort 
ofBSort env name l t = either (Misc.errorP "error-ofBSort" . F.showpp) id (ofBSortE env name l t)

ofBSortE :: Env -> ModName -> F.SourcePos -> BSort -> Either UserError RSort 
ofBSortE env name l t = ofBRType env name id l t 
  
ofBPVar :: Env -> ModName -> F.SourcePos -> BPVar -> RPVar
ofBPVar env name l = fmap (ofBSort env name l) 

--------------------------------------------------------------------------------
-- mkSpecType :: Env -> ModName -> F.SourcePos -> BareType -> SpecType
-- mkSpecType env name l t = mkSpecType' env name l πs t
  -- where 
    -- πs                  = ty_preds (toRTypeRep t)

mkSpecType' :: Env -> ModName -> F.SourcePos -> [PVar BSort] -> BareType -> SpecType
mkSpecType' env name l πs t = case ofBRType env name resolveReft l t of 
                                Left e  -> Misc.errorP "error-mkSpecType'" $ F.showpp e -- Ex.throw e 
                                Right v -> v 
  where
    resolveReft             = qualify env name . txParam l RT.subvUReft (RT.uPVar <$> πs) t

txParam :: F.SourcePos-> ((UsedPVar -> UsedPVar) -> t) -> [UsedPVar] -> RType c tv r -> t
txParam l f πs t = f (txPvar l (predMap πs t))

txPvar :: F.SourcePos -> M.HashMap F.Symbol UsedPVar -> UsedPVar -> UsedPVar
txPvar l m π = π { pargs = args' }
  where
    args' | not (null (pargs π)) = zipWith (\(_,x ,_) (t,_,y) -> (t, x, y)) (pargs π') (pargs π)
          | otherwise            = pargs π'
    π'    = Mb.fromMaybe err $ M.lookup (pname π) m
    err   = uError $ ErrUnbPred sp (pprint π)
    sp    = GM.sourcePosSrcSpan l 

predMap :: [UsedPVar] -> RType c tv r -> M.HashMap F.Symbol UsedPVar
predMap πs t = M.fromList [(pname π, π) | π <- πs ++ rtypePredBinds t]

rtypePredBinds :: RType c tv r -> [UsedPVar]
rtypePredBinds = map RT.uPVar . ty_preds . toRTypeRep

--------------------------------------------------------------------------------
type Expandable r = ( PPrint r
                    , F.Reftable r
                    , SubsTy RTyVar (RType RTyCon RTyVar ()) r
                    , F.Reftable (RTProp RTyCon RTyVar r))

ofBRType :: (Expandable r) => Env -> ModName -> (r -> r) -> F.SourcePos -> BRType r 
         -> Either UserError (RRType r)
ofBRType env name f l t  = go t 
  where
    goReft r             = return (f r) 
    goRImpF x t1 t2 r    = RImpF x <$> (rebind x <$> go t1) <*> go t2 <*> goReft r
    goRFun x t1 t2 r     = RFun  x <$> (rebind x <$> go t1) <*> go t2 <*> goReft r
    rebind x t           = F.subst1 t (x, F.EVar $ rTypeValueVar t)
    go (RAppTy t1 t2 r)  = RAppTy <$> go t1 <*> go t2 <*> goReft r
    go (RApp tc ts rs r) = goRApp tc ts rs r 
    go (RImpF x t1 t2 r) = goRImpF x t1 t2 r 
    go (RFun  x t1 t2 r) = goRFun  x t1 t2 r 
    go (RVar a r)        = RVar (RT.bareRTyVar a) <$> goReft r
    go (RAllT a t)       = RAllT a' <$> go t 
      where a'           = dropTyVarInfo (mapTyVarValue RT.bareRTyVar a) 
    go (RAllP a t)       = RAllP a' <$> go t 
      where a'           = ofBPVar env name l a 
    go (RAllS x t)       = RAllS x  <$> go t
    go (RAllE x t1 t2)   = RAllE x  <$> go t1    <*> go t2
    go (REx x t1 t2)     = REx   x  <$> go t1    <*> go t2
    go (RRTy xts r o t)  = RRTy  <$> xts' <*> (goReft r) <*> (pure o) <*> go t
      where xts'         = mapM (Misc.mapSndM go) xts
    go (RHole r)         = RHole    <$> goReft r
    go (RExprArg le)     = return    $ RExprArg (qualify env name le) 
    goRef (RProp ss (RHole r)) = rPropP <$> (mapM goSyms ss) <*> goReft r
    goRef (RProp ss t)         = RProp  <$> (mapM goSyms ss) <*> go t
    goSyms (x, t)              = (x,) <$> ofBSortE env name l t 
    goRApp tc ts rs r          = bareTCApp <$> goReft r <*> lc' <*> mapM goRef rs <*> mapM go ts
      where
        lc'                    = F.atLoc lc <$> matchTyCon env name lc (length ts)
        lc                     = btc_tc tc
    -- goRApp _ _ _ _             = impossible Nothing "goRApp failed through to final case"

{- 
    -- TODO-REBARE: goRImpF bounds _ (RApp c ps' _ _) t _
    -- TODO-REBARE:  | Just bnd <- M.lookup (btc_tc c) bounds
    -- TODO-REBARE:   = do let (ts', ps) = splitAt (length $ tyvars bnd) ps'
    -- TODO-REBARE:        ts <- mapM go ts'
    -- TODO-REBARE:        makeBound bnd ts [x | RVar (BTV x) _ <- ps] <$> go t
    -- TODO-REBARE: goRFun bounds _ (RApp c ps' _ _) t _
    -- TODO-REBARE: | Just bnd <- M.lookup (btc_tc c) bounds
    -- TODO-REBARE: = do let (ts', ps) = splitAt (length $ tyvars bnd) ps'
    -- TODO-REBARE: ts <- mapM go ts'
    -- TODO-REBARE: makeBound bnd ts [x | RVar (BTV x) _ <- ps] <$> go t

  -- TODO-REBARE: ofBareRApp env name t@(F.Loc _ _ !(RApp tc ts _ r))
  -- TODO-REBARE: | Loc l _ c <- btc_tc tc
  -- TODO-REBARE: , Just rta <- M.lookup c aliases
  -- TODO-REBARE: = appRTAlias l rta ts =<< resolveReft r

-}

matchTyCon :: Env -> ModName -> LocSymbol -> Int -> Either UserError Ghc.TyCon
matchTyCon env name lc@(Loc _ _ c) arity
  | isList c && arity == 1  = knownTC Ghc.listTyCon
  | isTuple c               = knownTC tuplTc 
  | otherwise               = resolveLocSym env name msg lc 
  where 
    msg                     = "MATCH-TYCON: " ++ F.showpp c
    tuplTc                  = Ghc.tupleTyCon Ghc.Boxed arity 
    knownTC                 = resolveLocSym env name "knownTyCon" . GM.namedLocSymbol 

-- knownTyCon :: Env -> ModName -> Ghc.TyCon -> Either UserError Ghc.TyCon 
-- knownTyCon env name tc = 
--  where 
--    lx                 = GM.locNamedThing tc

bareTCApp :: (Expandable r) 
          => r
          -> Located Ghc.TyCon
          -> [RTProp RTyCon RTyVar r]
          -> [RType RTyCon RTyVar r]
          -> (RType RTyCon RTyVar r)
bareTCApp r (Loc l _ c) rs ts | Just rhs <- Ghc.synTyConRhs_maybe c
  = if (GM.kindTCArity c < length ts) 
      then error (F.showpp err)
      else tyApp (RT.subsTyVars_meet su $ RT.ofType rhs) (drop nts ts) rs r
    where
       tvs = [ v | (v, b) <- zip (GM.tyConTyVarsDef c) (Ghc.tyConBinders c), GM.isAnonBinder b]
       su  = zipWith (\a t -> (RT.rTyVar a, toRSort t, t)) tvs ts
       nts = length tvs

       err :: UserError
       err = ErrAliasApp (GM.sourcePosSrcSpan l) (pprint c) (Ghc.getSrcSpan c)
                         (PJ.hcat [ PJ.text "Expects"
                                  , pprint (GM.realTcArity c) 
                                  , PJ.text "arguments, but is given" 
                                  , pprint (length ts) ] )
-- TODO expandTypeSynonyms here to
bareTCApp r (Loc _ _ c) rs ts | Ghc.isFamilyTyCon c && isTrivial t
  = expandRTypeSynonyms (t `RT.strengthen` r)
  where t = RT.rApp c ts rs mempty

bareTCApp r (Loc _ _ c) rs ts
  = RT.rApp c ts rs r


tyApp :: F.Reftable r => RType c tv r -> [RType c tv r] -> [RTProp c tv r] -> r 
      -> RType c tv r
tyApp (RApp c ts rs r) ts' rs' r' = RApp c (ts ++ ts') (rs ++ rs') (r `F.meet` r')
tyApp t                []  []  r  = t `RT.strengthen` r
tyApp _                 _  _   _  = panic Nothing $ "Bare.Type.tyApp on invalid inputs"

expandRTypeSynonyms :: (Expandable r) => RRType r -> RRType r
expandRTypeSynonyms = RT.ofType . Ghc.expandTypeSynonyms . RT.toType
                   


------------------------------------------------------------------------------------------
-- | Is this the SAME as addTyConInfo? No. `txRefSort`
-- (1) adds the _real_ sorts to RProp,
-- (2) gathers _extra_ RProp at turns them into refinements,
--     e.g. tests/pos/multi-pred-app-00.hs
------------------------------------------------------------------------------------------

txRefSort :: TyConMap -> F.TCEmb Ghc.TyCon -> LocSpecType -> LocSpecType
txRefSort tyi tce t = F.atLoc t $ mapBot (addSymSort (GM.fSrcSpan t) tce tyi) (val t)

addSymSort :: (PPrint t, F.Reftable t)
           => Ghc.SrcSpan
           -> F.TCEmb Ghc.TyCon
           -> M.HashMap Ghc.TyCon RTyCon
           -> RType RTyCon RTyVar (UReft t)
           -> RType RTyCon RTyVar (UReft t)
addSymSort sp tce tyi (RApp rc@(RTyCon {}) ts rs r)
  = RApp rc ts (zipWith3 (addSymSortRef sp rc) pvs rargs [1..]) r'
  where
    rc'                = RT.appRTyCon tce tyi rc ts
    pvs                = rTyConPVs rc'
    (rargs, rrest)     = splitAt (length pvs) rs
    r'                 = L.foldl' go r rrest
    go r (RProp _ (RHole r')) = r' `F.meet` r
    go r (RProp  _ t' )       = let r' = Mb.fromMaybe mempty (stripRTypeBase t') in r `F.meet` r'

addSymSort _ _ _ t
  = t

addSymSortRef :: (PPrint t, PPrint a, F.Symbolic tv, F.Reftable t)
              => Ghc.SrcSpan
              -> a
              -> PVar (RType c tv ())
              -> Ref (RType c tv ()) (RType c tv (UReft t))
              -> Int
              -> Ref (RType c tv ()) (RType c tv (UReft t))
addSymSortRef sp rc p r i
  | isPropPV p
  = addSymSortRef' sp rc i p r
  | otherwise
  = panic Nothing "addSymSortRef: malformed ref application"

addSymSortRef' :: (PPrint t, PPrint a, F.Symbolic tv, F.Reftable t)
               => Ghc.SrcSpan
               -> a
               -> Int
               -> PVar (RType c tv ())
               -> Ref (RType c tv ()) (RType c tv (UReft t))
               -> Ref (RType c tv ()) (RType c tv (UReft t))
addSymSortRef' _ _ _ p (RProp s (RVar v r)) | isDummy v
  = RProp xs t
    where
      t  = ofRSort (pvType p) `RT.strengthen` r
      xs = spliceArgs "addSymSortRef 1" s p

addSymSortRef' sp rc i p (RProp _ (RHole r@(MkUReft _ (Pr [up]) _)))
  | length xs == length ts
  = RProp xts (RHole r)
  | otherwise
  = uError $ ErrPartPred sp (pprint rc) (pprint $ pname up) i (length xs) (length ts)
    where
      xts = Misc.safeZipWithError "addSymSortRef'" xs ts
      xs  = Misc.snd3 <$> pargs up
      ts  = Misc.fst3 <$> pargs p

addSymSortRef' _ _ _ _ (RProp s (RHole r))
  = RProp s (RHole r)

addSymSortRef' _ _ _ p (RProp s t)
  = RProp xs t
    where
      xs = spliceArgs "addSymSortRef 2" s p

spliceArgs :: String  -> [(F.Symbol, b)] -> PVar t -> [(F.Symbol, t)]
spliceArgs msg s p = go (fst <$> s) (pargs p)
  where
    go []     []           = []
    go []     ((s,x,_):as) = (x, s):go [] as
    go (x:xs) ((s,_,_):as) = (x,s):go xs as
    go xs     []           = panic Nothing $ "spliceArgs: " ++ msg ++ "on XS=" ++ show xs

