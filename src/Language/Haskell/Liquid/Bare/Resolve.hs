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
  , qualifyTop
  
  -- * Looking up names
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

  -- * Post-processing types
  , txRefSort

  -- * Fixing local variables
  , resolveLocalBinds 
  ) where 

-- import qualified Control.Exception as Ex 
import qualified Data.List                         as L 
import qualified Data.HashSet                      as S 
import qualified Data.Maybe                        as Mb
import qualified Data.HashMap.Strict               as M
import qualified Text.PrettyPrint.HughesPJ         as PJ 

import qualified Language.Fixpoint.Types               as F 
import qualified Language.Fixpoint.Types.Visitor       as F 
import qualified Language.Fixpoint.Misc                as Misc 

import qualified Language.Haskell.Liquid.GHC.API       as Ghc 
import qualified Language.Haskell.Liquid.GHC.Misc      as GM 
import qualified Language.Haskell.Liquid.Misc          as Misc 
import qualified Language.Haskell.Liquid.Types.RefType as RT
import           Language.Haskell.Liquid.Types.Types   
import           Language.Haskell.Liquid.Types.Specs 
import           Language.Haskell.Liquid.Types.Visitors 
import           Language.Haskell.Liquid.Bare.Types 
import           Language.Haskell.Liquid.Bare.Misc   
import           Language.Haskell.Liquid.WiredIn 

-------------------------------------------------------------------------------
-- | Creating an environment 
-------------------------------------------------------------------------------
makeEnv :: Config -> GhcSrc -> LogicMap -> [(ModName, BareSpec)] -> Env 
makeEnv cfg src lmap specs = RE 
  { reLMap      = lmap
  , reSyms      = syms 
  , _reSubst    = makeVarSubst   src 
  , _reTyThings = makeTyThingMap src 
  , reQualImps  = gsQualImps     src
  , reAllImps   = gsAllImps      src
  , reLocalVars = makeLocalVars  src 
  , reCbs       = giCbs          src
  , reGlobSyms  = S.fromList     globalSyms 
  , reCfg       = cfg
  } 
  where 
    globalSyms  = concatMap getGlobalSyms specs
    syms        = [ (F.symbol v, v) | v <- vars ] 
    vars        = srcVars src

getGlobalSyms :: (ModName, BareSpec) -> [F.Symbol]
getGlobalSyms (_, spec) 
  = filter (not . GM.isQualifiedSym) 
       $ (mbName <$> measures  spec) 
      ++ (mbName <$> cmeasures spec)
      ++ (mbName <$> imeasures spec)
  where 
    mbName = F.val . msName

makeLocalVars :: GhcSrc -> LocalVars 
makeLocalVars = localVarMap . localBinds . giCbs

-- TODO: rewrite using CoreVisitor
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
    go  g (Ghc.Lam _ e)       = go g e
    go  g (Ghc.Let b e)       = bgo g b ++ go (adds b g) e 
    go  g (Ghc.Tick _ e)      = go g e
    go  g (Ghc.Cast e _)      = go g e
    go  g (Ghc.Case e _ _ cs) = go g e ++ concatMap (go g . Misc.thd3) cs
    go  _ (Ghc.Var _)         = []
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
  Misc.group [ (x, (m, t))  | t         <- srcThings src
                            , let (m, x) = qualifiedSymbol t 
                            , not (isLocal m)
             ] 

isLocal :: F.Symbol -> Bool
isLocal = isEmptySymbol 

qualifiedSymbol :: (F.Symbolic a) => a -> (F.Symbol, F.Symbol)
qualifiedSymbol = splitModuleNameExact . F.symbol 

isEmptySymbol :: F.Symbol -> Bool 
isEmptySymbol x = F.lengthSym x == 0 

srcThings :: GhcSrc -> [Ghc.TyThing] 
srcThings src = F.tracepp "SRC-THINGS" $ 
                Misc.hashNubWith F.showpp (gsTyThings src ++ mySrcThings src) 

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

-- | We prioritize the @Ghc.Var@ in @srcVars@ because @giDefVars@ and @gsTyThings@ 
--   have _different_ values for the same binder, with different types where the 
--   type params are alpha-renamed. However, for absref, we need _the same_ 
--   type parameters as used by GHC as those are used inside the lambdas and
--   other bindings in the code. See also [NOTE: Plug-Holes-TyVars] and 
--      tests-absref-pos-Papp00.hs 

srcVars :: GhcSrc -> [Ghc.Var]
srcVars src = filter Ghc.isId .  fmap Misc.thd3 . Misc.fstByRank $ concat 
  [ key "SRC-VAR-DEF" 0 <$> giDefVars src 
  , key "SRC-VAR-DER" 1 <$> giDerVars src
  , key "SRC-VAR-IMP" 2 <$> giImpVars src 
  , key "SRC-VAR-USE" 3 <$> giUseVars src 
  , key "SRC-VAR-THN" 4 <$> [ x | Ghc.AnId x <- gsTyThings src ]
  ]
  where 
    key :: String -> Int -> Ghc.Var -> (Int, F.Symbol, Ghc.Var)
    key _ i x  = (i, F.symbol x, {- dump s -} x) 
    _dump msg x = fst . F.notracepp msg $ (x, RT.ofType (Ghc.expandTypeSynonyms (Ghc.varType x)) :: SpecType)

dataConVars :: [Ghc.DataCon] -> [Ghc.Var]
dataConVars dcs = concat 
  [ Ghc.dataConWorkId <$> dcs 
  , Ghc.dataConWrapId <$> dcs 
  ] 
-------------------------------------------------------------------------------
-- | Qualify various names 
-------------------------------------------------------------------------------
qualifyTop :: (Qualify a) => Env -> ModName -> a -> a 
qualifyTop env name = qualify env name []

class Qualify a where 
  qualify :: Env -> ModName -> [F.Symbol] -> a -> a 

instance Qualify TyConP where 
  qualify env name bs tcp = tcp { tcpSizeFun = qualify env name bs <$> tcpSizeFun tcp }

instance Qualify SizeFun where 
  qualify env name bs (SymSizeFun lx) = SymSizeFun (qualify env name bs lx)
  qualify _   _    _ sf              = sf

instance Qualify F.Equation where 
  qualify _env _name _bs x = x -- TODO-REBARE 
-- REBARE: qualifyAxiomEq :: Bare.Env -> Var -> Subst -> AxiomEq -> AxiomEq
-- REBARE: qualifyAxiomEq v su eq = subst su eq { eqName = symbol v}

instance Qualify F.Symbol where 
  qualify env name bs x = F.notracepp ("qualifySymbol: " ++ F.showpp x) $ 
                            qualifySymbol env name bs x 

qualifySymbol :: Env -> ModName -> [F.Symbol] -> F.Symbol -> F.Symbol                                                   
qualifySymbol env name bs x
  | isSpl     = x 
  | otherwise = case resolveSym env name "Symbol" x of 
                  Left  _ -> x 
                  Right v -> v 
  where 
    isSpl     = isSplSymbol env bs x

isSplSymbol :: Env -> [F.Symbol] -> F.Symbol -> Bool 
isSplSymbol env bs x 
  =  isWiredInName x 
  || elem x bs 
  || S.member x (reGlobSyms env) 

-- REBARE: qualifySymbol :: Env -> F.Symbol -> F.Symbol
-- REBARE: qualifySymbol env x = maybe x F.symbol (M.lookup x syms)

instance (Qualify a) => Qualify (Located a) where 
  qualify env name bs = fmap (qualify env name bs) 

instance (Qualify a) => Qualify [a] where 
  qualify env name bs = fmap (qualify env name bs) 

instance (Qualify a) => Qualify (Maybe a) where 
  qualify env name bs = fmap (qualify env name bs) 

instance Qualify Body where 
  qualify env name bs (P   p) = P   (qualify env name bs p) 
  qualify env name bs (E   e) = E   (qualify env name bs e)
  qualify env name bs (R x p) = R x (qualify env name bs p)

instance Qualify TyConInfo where 
  qualify env name bs tci = tci { sizeFunction = qualify env name bs <$> sizeFunction tci }

instance Qualify RTyCon where 
  qualify env name bs rtc = rtc { rtc_info = qualify env name bs (rtc_info rtc) }

instance Qualify (Measure SpecType Ghc.DataCon) where 
  qualify env name bs m = m -- FIXME substEnv env name bs $ 
    { msName = qualify env name bs     (msName m) 
    , msEqns = qualify env name bs <$> (msEqns m) }

instance Qualify (Def ty ctor) where 
  qualify env name bs d = d 
    { body  = qualify env name (bs ++ bs') (body d) } 
    where 
      bs'   = fst <$> binds d

instance Qualify BareMeasure where 
  qualify env name bs m = m 
    { msEqns = qualify env name bs (msEqns m)
    } 

instance Qualify DataCtor where 
  qualify env name bs c = c
    { dcTheta  = qualify env name bs (dcTheta  c) 
    , dcFields = qualify env name bs (dcFields c) 
    , dcResult = qualify env name bs (dcResult c)
    }
 
instance Qualify DataDecl where 
  qualify env name bs d = d 
    { tycDCons  = qualify env name bs (tycDCons  d)
    , tycPropTy = qualify env name bs (tycPropTy d) 
    } 

instance Qualify ModSpecs where 
  qualify env name bs = Misc.hashMapMapWithKey (\_ -> qualify env name bs) 

instance Qualify b => Qualify (a, b) where 
  qualify env name bs (x, y) = (x, qualify env name bs y)

instance Qualify BareSpec where 
  qualify = qualifyBareSpec 

qualifyBareSpec :: Env -> ModName -> [F.Symbol] -> BareSpec -> BareSpec 
qualifyBareSpec env name bs sp = sp 
  { measures   = qualify env name bs (measures   sp) 
  , asmSigs    = qualify env name bs (asmSigs    sp)
  , sigs       = qualify env name bs (sigs       sp)
  , localSigs  = qualify env name bs (localSigs  sp)
  , reflSigs   = qualify env name bs (reflSigs   sp)
  , dataDecls  = qualify env name bs (dataDecls  sp)
  , newtyDecls = qualify env name bs (newtyDecls sp)
  , ialiases   = [ (f x, f y) | (x, y) <- ialiases sp ]
  } 
  where f      = qualify env name bs 

instance Qualify F.Expr where 
  qualify = substEnv 

instance Qualify RReft where 
  qualify = substEnv 

instance Qualify F.Qualifier where 
  qualify env name bs q = q { F.qBody = qualify env name bs' (F.qBody q) } 
    where 
      bs'               = bs ++ (F.qpSym <$> F.qParams q)

substEnv :: (F.Subable a) => Env -> ModName -> [F.Symbol] -> a -> a 
substEnv env name bs = F.substa (qualifySymbol env name bs) 

instance Qualify SpecType where 
  qualify = substFreeEnv           

instance Qualify BareType where 
  qualify = substFreeEnv 

-- Do not substitute variables bound e.g. by function types
substFreeEnv :: (F.Subable a) => Env -> ModName -> [F.Symbol] -> a -> a 
substFreeEnv env name bs = F.substf (F.EVar . qualifySymbol env name bs) 

-------------------------------------------------------------------------------
lookupGhcNamedVar :: (Ghc.NamedThing a, F.Symbolic a) => Env -> ModName -> a -> Maybe Ghc.Var
-------------------------------------------------------------------------------
lookupGhcNamedVar env name z = maybeResolveSym  env name "Var" lx
                               -- strictResolveSym env name "Var" lx 
  where 
    lx                       = GM.namedLocSymbol z

lookupGhcVar :: Env -> ModName -> String -> LocSymbol -> Ghc.Var 
lookupGhcVar env name kind lx = 
  case resolveLocSym env name kind lx of 
    Right v -> Mb.fromMaybe v       (lookupLocalVar env lx [v]) 
    Left  e -> Mb.fromMaybe (err e) (lookupLocalVar env lx []) 
  where
    err e   = Misc.errorP "error-lookupGhcVar" (F.showpp e)

-- | @lookupLocalVar@ takes as input the list of "global" (top-level) vars 
--   that also match the name @lx@; we then pick the "closest" definition. 
--   See tests/names/LocalSpec.hs for a motivating example. 

lookupLocalVar :: Env -> LocSymbol -> [Ghc.Var] -> Maybe Ghc.Var
lookupLocalVar env lx gvs = Misc.findNearest (F.srcLine lx) kvs
  where 
    kvs                   = M.lookupDefault gs x (reLocalVars env) 
    gs                    = [(F.srcLine v, v) | v <- gvs]
    _xn                   = F.srcLine lx  
    (_, x)                = unQualifySymbol (F.val lx)


lookupGhcDataCon :: Env -> ModName -> String -> LocSymbol -> Ghc.DataCon 
lookupGhcDataCon = strictResolveSym 

lookupGhcTyCon :: Env -> ModName -> String -> LocSymbol -> Ghc.TyCon 
lookupGhcTyCon env name k lx = F.notracepp ("LOOKUP-TYCON: " ++ F.showpp (val lx)) 
                             $ strictResolveSym env name k lx

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
knownGhcType env name (F.Loc l _ t) = 
  case ofBareTypeE env name l Nothing t of 
    Left e  -> F.notracepp ("knownType: " ++ F.showpp (t, e)) $ False 
    Right _ -> True 

_rTypeTyCons :: (Ord c) => RType c tv r -> [c]
_rTypeTyCons           = Misc.sortNub . foldRType f []   
  where 
    f acc t@(RApp {}) = rt_tycon t : acc 
    f acc _           = acc

-- Aargh. Silly that each of these is the SAME code, only difference is the type.

knownGhcVar :: Env -> ModName -> LocSymbol -> Bool 
knownGhcVar env name lx = Mb.isJust v 
  where 
    v :: Maybe Ghc.Var -- This annotation is crucial
    v = F.notracepp ("knownGhcVar " ++ F.showpp lx) 
      $ maybeResolveSym env name "known-var" lx 

knownGhcTyCon :: Env -> ModName -> LocSymbol -> Bool 
knownGhcTyCon env name lx = F.notracepp  msg $ Mb.isJust v 
  where 
    msg = ("knownGhcTyCon: "  ++ F.showpp lx)
    v :: Maybe Ghc.TyCon -- This annotation is crucial
    v = maybeResolveSym env name "known-tycon" lx 

knownGhcDataCon :: Env -> ModName -> LocSymbol -> Bool 
knownGhcDataCon env name lx = Mb.isJust v 
  where 
    v :: Maybe Ghc.DataCon -- This annotation is crucial
    v = F.notracepp ("knownGhcDataCon" ++ F.showpp lx) 
      $ maybeResolveSym env name "known-datacon" lx 

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

resolveWith :: (PPrint a) => (Ghc.TyThing -> Maybe a) -> Env -> ModName -> String -> LocSymbol 
            -> Either UserError a 
resolveWith f env name kind lx =
  case Mb.mapMaybe f things of 
    []  -> Left  (errResolve kind lx) 
    [x] -> Right x 
    -- xs  -> error ("Oh-no: " ++ kind ++ ":" ++ F.showpp things)
    -- xs  -> Left $ ErrDupNames sp (PJ.text "GOO") [] -- (pprint (F.symbol lx)) [] -- (pprint <$> xs)
    xs  -> Left $ ErrDupNames sp (pprint (F.val lx)) (pprint <$> xs)
  where 
    _xSym  = (F.val lx)
    sp     = GM.fSrcSpanSrcSpan (F.srcSpan lx)
    things = F.notracepp msg $ lookupTyThing env name (val lx) 
    msg    = "resolveWith: " ++ kind ++ " " ++ F.showpp (val lx)

-------------------------------------------------------------------------------
-- | @lookupTyThing@ is the central place where we lookup the @Env@ to find 
--   any @Ghc.TyThing@ that match that name. The code is a bit hairy as we
--   have various heuristics to approximiate how GHC resolves names. e.g. 
--   see tests-names-pos-*.hs, esp. vector04.hs where we need the name `Vector` 
--   to resolve to `Data.Vector.Vector` and not `Data.Vector.Generic.Base.Vector`... 
-------------------------------------------------------------------------------
lookupTyThing :: Env -> ModName -> F.Symbol -> [Ghc.TyThing]
-------------------------------------------------------------------------------
lookupTyThing env name sym = case Misc.sortOn fst (Misc.groupList matches) of 
                               (_,ts):_ -> ts
                               []       -> []
  where 
    matches                = [ ((k, m), t) | (m, t) <- lookupThings env x
                                           , k      <- F.notracepp msg $ mm nameSym m mods ]
    msg                    = "lookupTyThing: " ++ F.showpp (sym, x, mods)
    (x, mods)              = symbolModules env sym
    nameSym                = F.symbol name
    mm name m mods           = F.notracepp ("matchMod: " ++ F.showpp (sym, name, m, mods)) $ 
                              matchMod env name m mods 

lookupThings :: Env -> F.Symbol -> [(F.Symbol, Ghc.TyThing)] 
lookupThings env x = F.notracepp ("lookupThings: " ++ F.showpp x) 
                   $ Misc.fromFirstMaybes [] (get <$> [x, GM.stripParensSym x])
  where 
    get z          = M.lookup z (_reTyThings env)

matchMod :: Env -> F.Symbol -> F.Symbol -> Maybe [F.Symbol] -> [Int]
matchMod env tgtName defName Nothing     
  | defName == tgtName = [0]                       -- prioritize names defined in *this* module 
  | otherwise          = [matchImp env defName 1]  -- prioritize directly imported modules over 
                                                   -- names coming from elsewhere, with a 
                                                    

matchMod env tgtName defName (Just ms)   
  |  isEmptySymbol defName 
  && ms == [tgtName]   = [0]                       -- local variable, see tests-names-pos-local00.hs
  | ms == [defName]    = [1]
  | isExtMatch         = [matchImp env defName 2]  -- to allow matching re-exported names e.g. Data.Set.union for Data.Set.Internal.union
  | otherwise          = []  
  where 
    isExtMatch       = any (`F.isPrefixOfSym` defName) ms

symbolModules :: Env -> F.Symbol -> (F.Symbol, Maybe [F.Symbol])
symbolModules env s = (x, glerb <$> modMb) 
  where 
    (modMb, x)      = unQualifySymbol s 
    glerb m         = M.lookupDefault [m] m (reQualImps env) 

-- | @matchImp@ lets us prioritize @TyThing@ defined in directly imported modules over 
--   those defined elsewhere.
matchImp :: Env -> F.Symbol -> Int -> Int 
matchImp env defName i   
  | S.member defName (reAllImps env) = i 
  | otherwise                       = i + 1 

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
-- | @ofBareType@ and @ofBareTypeE@ should be the _only_ @SpecType@ constructors
-------------------------------------------------------------------------------
ofBareType :: Env -> ModName -> F.SourcePos -> Maybe [PVar BSort] -> BareType -> SpecType 
ofBareType env name l ps t = either (Misc.errorP "error-ofBareType" . F.showpp) id 
                              (ofBareTypeE env name l ps t)

ofBareTypeE :: Env -> ModName -> F.SourcePos -> Maybe [PVar BSort] -> BareType -> Either UserError SpecType 
ofBareTypeE env name l ps t = ofBRType env name (resolveReft env name l ps t) l t 

resolveReft :: Env -> ModName -> F.SourcePos -> Maybe [PVar BSort] -> BareType -> [F.Symbol] -> RReft -> RReft 
resolveReft env name l ps t bs
        = qualify env name bs 
        . txParam l RT.subvUReft (RT.uPVar <$> πs) t
        . fixReftTyVars t       -- same as fixCoercions 
  where 
    πs  = Mb.fromMaybe tπs ps  
    tπs = ty_preds (toRTypeRep t) 
     
fixReftTyVars :: BareType -> RReft -> RReft 
fixReftTyVars bt  = coSubRReft coSub 
  where
    coSub         = M.fromList [ (F.symbol a, F.FObj (specTvSymbol a)) | a <- tvs ]
    tvs           = RT.allTyVars bt
    specTvSymbol  = F.symbol . RT.bareRTyVar

coSubRReft :: F.CoSub -> RReft -> RReft 
coSubRReft su r = r { ur_reft = coSubReft su (ur_reft r) } 

coSubReft :: F.CoSub -> F.Reft -> F.Reft 
coSubReft su (F.Reft (x, e)) = F.Reft (x, F.applyCoSub su e)


ofBSort :: Env -> ModName -> F.SourcePos -> BSort -> RSort 
ofBSort env name l t = either (Misc.errorP "error-ofBSort" . F.showpp) id (ofBSortE env name l t)

ofBSortE :: Env -> ModName -> F.SourcePos -> BSort -> Either UserError RSort 
ofBSortE env name l t = ofBRType env name (const id) l t 
  
ofBPVar :: Env -> ModName -> F.SourcePos -> BPVar -> RPVar
ofBPVar env name l = fmap (ofBSort env name l) 

--------------------------------------------------------------------------------
-- REBARE mkSpecType' :: Env -> ModName -> F.SourcePos -> [PVar BSort] -> BareType -> SpecType
-- REBARE mkSpecType' env name l ps t = ofBareType env name l (Just ps) t 

-- REBARE mkSpecType :: Env -> ModName -> F.SourcePos -> BareType -> SpecType
-- REBARE mkSpecType env name l t = mkSpecType' env name l πs t
  -- REBARE where 
    -- REBARE πs                  = ty_preds (toRTypeRep t)

-- REBARE mkSpecType' env name l πs t = case ofBRType env name resolveReft l t of 
                                -- REBARE Left e  -> Misc.errorP "error-mkSpecType'" $ F.showpp e 
                                -- REBARE -- Ex.throw e 
                                -- REBARE Right v -> v 
  -- REBARE where
    -- REBARE resolveReft             = qualify env name . txParam l RT.subvUReft (RT.uPVar <$> πs) t

txParam :: F.SourcePos -> ((UsedPVar -> UsedPVar) -> t) -> [UsedPVar] -> RType c tv r -> t
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

ofBRType :: (Expandable r) => Env -> ModName -> ([F.Symbol] -> r -> r) -> F.SourcePos -> BRType r 
         -> Either UserError (RRType r)
ofBRType env name f l t  = go [] t 
  where
    goReft bs r             = return (f bs r) 
    goRImpF bs x t1 t2 r    = RImpF x <$> (rebind x <$> go bs t1) <*> go (x:bs) t2 <*> goReft bs r
    goRFun  bs x t1 t2 r    = RFun  x <$> (rebind x <$> go bs t1) <*> go (x:bs) t2 <*> goReft bs r
    rebind x t              = F.subst1 t (x, F.EVar $ rTypeValueVar t)
    go bs (RAppTy t1 t2 r)  = RAppTy <$> go bs t1 <*> go bs t2 <*> goReft bs r
    go bs (RApp tc ts rs r) = goRApp bs tc ts rs r 
    go bs (RImpF x t1 t2 r) = goRImpF bs x t1 t2 r 
    go bs (RFun  x t1 t2 r) = goRFun  bs x t1 t2 r 
    go bs (RVar a r)        = RVar (RT.bareRTyVar a) <$> goReft bs r
    go bs (RAllT a t)       = RAllT a' <$> go bs t 
      where a'              = dropTyVarInfo (mapTyVarValue RT.bareRTyVar a) 
    go bs (RAllP a t)       = RAllP a' <$> go bs t 
      where a'              = ofBPVar env name l a 
    go bs (RAllS x t)       = RAllS x  <$> go bs t
    go bs (RAllE x t1 t2)   = RAllE x  <$> go bs t1    <*> go bs t2
    go bs (REx x t1 t2)     = REx   x  <$> go bs t1    <*> go (x:bs) t2
    go bs (RRTy xts r o t)  = RRTy  <$> xts' <*> (goReft bs r) <*> (pure o) <*> go bs t
      where xts'            = mapM (Misc.mapSndM (go bs)) xts
    go bs (RHole r)         = RHole    <$> goReft bs r
    go bs (RExprArg le)     = return    $ RExprArg (qualify env name bs le) 
    goRef bs (RProp ss (RHole r)) = rPropP <$> (mapM goSyms ss) <*> goReft bs r
    goRef bs (RProp ss t)         = RProp  <$> (mapM goSyms ss) <*> go bs t
    goSyms (x, t)                 = (x,) <$> ofBSortE env name l t 
    goRApp bs tc ts rs r          = bareTCApp <$> goReft bs r <*> lc' <*> mapM (goRef bs) rs <*> mapM (go bs) ts
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
  | isList c && arity == 1  = {- knownTC -} Right Ghc.listTyCon
  | isTuple c               = {- knownTC -} Right tuplTc 
  | otherwise               = resolveLocSym env name msg lc 
  where 
    msg                     = "matchTyCon: " ++ F.showpp c
    tuplTc                  = Ghc.tupleTyCon Ghc.Boxed arity 
    -- knownTC :: Int
    -- knownTC                 = resolveLocSym env name "knownTyCon" . GM.namedLocSymbol 

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

addSymSortRef' _sp rc i p (RProp _ (RHole r@(MkUReft _ (Pr [up]) _)))
  | length xs == length ts
  = RProp xts (RHole r)
  | otherwise
  = Misc.errorP "ZONK" $ F.showpp (rc, pname up, i, length xs, length ts)
  -- uError $ ErrPartPred sp (pprint rc) (pprint $ pname up) i (length xs) (length ts)
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

---------------------------------------------------------------------------------
-- RJ: formerly, `replaceLocalBinds` AFAICT
-- | @resolveLocalBinds@ resolves that the "free" variables that appear in the 
--   type-sigs for non-toplevel binders (that correspond to other locally bound)
--   source variables that are visible at that at non-top-level scope. 
--   e.g. tests-names-pos-local02.hs  
---------------------------------------------------------------------------------
resolveLocalBinds :: Env -> [(Ghc.Var, LocBareType)] -> [(Ghc.Var, LocBareType)]
---------------------------------------------------------------------------------
resolveLocalBinds env xts = topTs ++ replace locTs 
  where 
    (locTs, topTs)        = L.partition isLocalSig xts
    replace               = M.toList . replaceSigs (reCbs env) . M.fromList 
    isLocalSig            = Mb.isJust . localKey . fst
    -- replaceSigs :: [Ghc.CoreBind] -> SigMap -> SigMap 
    replaceSigs cbs sigm  = coreVisitor replaceVisitor M.empty sigm cbs 

replaceVisitor :: CoreVisitor SymMap SigMap 
replaceVisitor = CoreVisitor { envF  = addBind, bindF = updSigMap, exprF = \_ m _ -> m }

addBind :: SymMap -> Ghc.Var -> SymMap 
addBind env v = case localKey v of 
  Just vx -> M.insert vx (F.symbol v) env 
  Nothing -> env
    
updSigMap :: SymMap -> SigMap -> Ghc.Var -> SigMap 
updSigMap env m v = case M.lookup v m of 
  Nothing -> m 
  Just t  -> M.insert v (F.substf (F.EVar . qualifySymMap env) t) m

qualifySymMap :: SymMap -> F.Symbol -> F.Symbol 
qualifySymMap env x = M.lookupDefault x x env 

type SigMap = M.HashMap Ghc.Var  LocBareType 
type SymMap = M.HashMap F.Symbol F.Symbol

