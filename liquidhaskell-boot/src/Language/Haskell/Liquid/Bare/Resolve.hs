-- | This module has the code that uses the GHC definitions to:
--   1. MAKE a name-resolution environment,
--   2. USE the environment to translate plain symbols into Var, TyCon, etc.

{-# LANGUAGE OverloadedStrings     #-}
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
  , Lookup
  , qualifyTop, qualifyTopDummy, qualifyLocSymbolTop

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
  , coSubRReft
  , unQualifySymbol

  -- * Conversions from Bare
  , ofBareTypeE
  , ofBareType
  , ofBPVar

  -- * Post-processing types
  , txRefSort
  , errResolve

  -- * Fixing local variables
  , resolveLocalBinds
  , partitionLocalBinds
  ) where

import qualified Control.Exception                 as Ex
import           Control.Monad (mplus)
import qualified Data.List                         as L
import qualified Data.HashSet                      as S
import qualified Data.Maybe                        as Mb
import qualified Data.HashMap.Strict               as M
import qualified Data.Text                         as T
import qualified Text.PrettyPrint.HughesPJ         as PJ

import qualified Language.Fixpoint.Types               as F
import qualified Language.Fixpoint.Types.Visitor       as F
import qualified Language.Fixpoint.Misc                as Misc
import qualified Liquid.GHC.API       as Ghc
import qualified Language.Haskell.Liquid.GHC.Misc      as GM
import qualified Language.Haskell.Liquid.Misc          as Misc
import qualified Language.Haskell.Liquid.Types.RefType as RT
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Measure       (BareSpec)
import           Language.Haskell.Liquid.Types.Specs   hiding (BareSpec)
import           Language.Haskell.Liquid.Types.Visitors
import           Language.Haskell.Liquid.Bare.Types
import           Language.Haskell.Liquid.Bare.Misc
import           Language.Haskell.Liquid.WiredIn

myTracepp :: (F.PPrint a) => String -> a -> a
myTracepp = F.notracepp

-- type Lookup a = Misc.Validate [Error] a
type Lookup a = Either [Error] a

-------------------------------------------------------------------------------
-- | Creating an environment
-------------------------------------------------------------------------------
makeEnv :: Config -> GhcSrc -> LogicMap -> [(ModName, BareSpec)] -> Env
makeEnv cfg src lmap specs = RE
  { reLMap      = lmap
  , reSyms      = syms
  , _reSubst    = makeVarSubst   src
  , _reTyThings = makeTyThingMap src
  , reQualImps  = _gsQualImps     src
  , reAllImps   = _gsAllImps      src
  , reLocalVars = makeLocalVars  src
  , reSrc       = src
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
      ++ (mbName <$> omeasures spec)
  where
    mbName = F.val . msName

makeLocalVars :: GhcSrc -> LocalVars
makeLocalVars = localVarMap . localBinds . _giCbs

-- TODO: rewrite using CoreVisitor
localBinds :: [Ghc.CoreBind] -> [Ghc.Var]
localBinds                    = concatMap (bgo S.empty)
  where
    add  x g                  = maybe g (`S.insert` g) (localKey x)
    adds b g                  = foldr add g (Ghc.bindersOf b)
    take' x g                 = maybe [] (\k -> [x | not (S.member k g)]) (localKey x)
    pgo g (x, e)              = take' x g ++ go (add x g) e
    bgo g (Ghc.NonRec x e)    = pgo g (x, e)
    bgo g (Ghc.Rec xes)       = concatMap (pgo g) xes
    go  g (Ghc.App e a)       = concatMap (go  g) [e, a]
    go  g (Ghc.Lam _ e)       = go g e
    go  g (Ghc.Let b e)       = bgo g b ++ go (adds b g) e
    go  g (Ghc.Tick _ e)      = go g e
    go  g (Ghc.Cast e _)      = go g e
    go  g (Ghc.Case e _ _ cs) = go g e ++ concatMap (go g . (\(Ghc.Alt _ _ e') -> e')) cs
    go  _ (Ghc.Var _)         = []
    go  _ _                   = []

localVarMap :: [Ghc.Var] -> LocalVars
localVarMap vs =
  Misc.group [ (x, (i, v)) | v <- vs
                           , let i = F.unPos (F.srcLine v)
                           , x <- Mb.maybeToList (localKey v)
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
                       | (x, mxs) <- M.toList (makeSymMap src)
                       , not (isWiredInName x)
                       , v <- Mb.maybeToList (okUnqualified me mxs)
                   ]
    me           = F.symbol (_giTargetMod src)

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
  addListTyConName $
  Misc.group [ (x, (m, t))  | t         <- srcThings src
                            , tSym      <- Mb.maybeToList (tyThingSymbol t)
                            , let (m, x) = qualifiedSymbol tSym
                            , not (isLocal m)
             ]
  where
    -- We add the TyThing for the List constructor here. Otherwise, we
    -- lookups in the TyThingMap will fail for "List" and not for "[]".
    addListTyConName m =
      case M.lookup "[]" m of
        Nothing -> m
        Just ps -> M.insertWith (++) "List" (filterListTyCon ps) m

    -- The TyCon name in the TyThing for @"[]"@ must be @"[]"@ apparently.
    --
    -- listTyCon uses "List", and that made later checks fail for some tests,
    -- so we cannot just return @[("GHC.Types", ATyCon listTyCon)]@
    --
    -- Returning the TyCon that GHC yields for @"[]"@ has later tests fail,
    -- because that TyCon has no associated data constructors.
    --
    -- The solution we adopted for now is to return listTyCon, and use
    -- the name from the TyThing that GHC returned.
    filterListTyCon ps =
      [ (mn, Ghc.ATyCon tc') | (mn, Ghc.ATyCon tc) <- ps
          , "GHC.Types" == mn
          , let tc' = Ghc.listTyCon { Ghc.tyConName = Ghc.tyConName tc }
      ]

tyThingSymbol :: Ghc.TyThing -> Maybe F.Symbol
tyThingSymbol (Ghc.AnId     x) = Just (F.symbol x)
tyThingSymbol (Ghc.ATyCon   c) = Just (F.symbol c)
tyThingSymbol (Ghc.AConLike d) = conLikeSymbol d
tyThingSymbol _tt              = Nothing -- panic Nothing ("TODO: tyThingSymbol" ++ showPpr tt)


conLikeSymbol :: Ghc.ConLike -> Maybe F.Symbol
conLikeSymbol (Ghc.RealDataCon d) = Just (F.symbol d)
conLikeSymbol _z                   = Nothing -- panic Nothing ("TODO: conLikeSymbol -- " ++ showPpr z)




isLocal :: F.Symbol -> Bool
isLocal = isEmptySymbol

qualifiedSymbol :: (F.Symbolic a) => a -> (F.Symbol, F.Symbol)
qualifiedSymbol = splitModuleNameExact . F.symbol

isEmptySymbol :: F.Symbol -> Bool
isEmptySymbol x = F.lengthSym x == 0

srcThings :: GhcSrc -> [Ghc.TyThing]
srcThings src = myTracepp "SRCTHINGS"
              $ Misc.hashNubWith F.showpp (_gsTyThings src ++ mySrcThings src)

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
  [ _gsTcs     src
  , _gsFiTcs   src
  , _gsPrimTcs src
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

-- | We prioritize the @Ghc.Var@ in @srcVars@ because @_giDefVars@ and @gsTyThings@
--   have _different_ values for the same binder, with different types where the
--   type params are alpha-renamed. However, for absref, we need _the same_
--   type parameters as used by GHC as those are used inside the lambdas and
--   other bindings in the code. See also [NOTE: Plug-Holes-TyVars] and
--      tests-absref-pos-Papp00.hs

srcVars :: GhcSrc -> [Ghc.Var]
srcVars src = filter Ghc.isId .  fmap Misc.thd3 . Misc.fstByRank $ concat
  [ key "SRC-VAR-DEF" 0 <$> _giDefVars src
  , key "SRC-VAR-DER" 1 <$> S.toList (_giDerVars src)
  , key "SRC-VAR-IMP" 2 <$> _giImpVars src
  , key "SRC-VAR-USE" 3 <$> _giUseVars src
  , key "SRC-VAR-THN" 4 <$> [ x | Ghc.AnId x <- _gsTyThings src ]
  ]
  where
    key :: String -> Int -> Ghc.Var -> (Int, F.Symbol, Ghc.Var)
    key _ i x  = (i, F.symbol x, {- dump s -} x)
    _dump msg x = fst . myTracepp msg $ (x, RT.ofType (Ghc.expandTypeSynonyms (Ghc.varType x)) :: SpecType)

dataConVars :: [Ghc.DataCon] -> [Ghc.Var]
dataConVars dcs = (Ghc.dataConWorkId <$> dcs) ++ (Ghc.dataConWrapId <$> dcs)

-------------------------------------------------------------------------------
-- | Qualify various names
-------------------------------------------------------------------------------
qualifyTop :: (Qualify a) => Env -> ModName -> F.SourcePos -> a -> a
qualifyTop env name l = qualify env name l []

qualifyTopDummy :: (Qualify a) => Env -> ModName -> a -> a
qualifyTopDummy env name = qualifyTop env name dummySourcePos

dummySourcePos :: F.SourcePos
dummySourcePos = F.loc (F.dummyLoc ())

class Qualify a where
  qualify :: Env -> ModName -> F.SourcePos -> [F.Symbol] -> a -> a

instance Qualify TyConMap where
  qualify env name l bs tyi = tyi
    { tcmTyRTy = tx <$> tcmTyRTy tyi
    , tcmFIRTy = tx <$> tcmFIRTy tyi
    }
    where
      tx :: (Qualify a) => a -> a
      tx = qualify env name l bs

instance Qualify TyConP where
  qualify env name _ bs tcp = tcp { tcpSizeFun = qualify env name (tcpLoc tcp) bs <$> tcpSizeFun tcp }

instance Qualify SizeFun where
  qualify env name _ bs (SymSizeFun lx) = SymSizeFun (qualify env name (F.loc lx) bs lx)
  qualify _   _    _ _  sf              = sf

instance Qualify F.Equation where
  qualify _env _name _l _bs x = x -- TODO-REBARE
-- REBARE: qualifyAxiomEq :: Bare.Env -> Var -> Subst -> AxiomEq -> AxiomEq
-- REBARE: qualifyAxiomEq v su eq = subst su eq { eqName = symbol v}

instance Qualify F.Symbol where
  qualify env name l bs x = qualifySymbol env name l bs x

qualifySymbol :: Env -> ModName -> F.SourcePos -> [F.Symbol] -> F.Symbol -> F.Symbol
qualifySymbol env name l bs x
  | isSpl     = x
  | otherwise = case resolveLocSym env name "Symbol" (F.Loc l l x) of
                  Left _ -> x
                  Right v -> v
  where
    isSpl     = isSplSymbol env bs x


qualifyLocSymbolTop :: Env -> ModName -> F.LocSymbol -> F.LocSymbol
qualifyLocSymbolTop env modName l  = l {val = qualifyTop env modName (loc l) (val l)}

isSplSymbol :: Env -> [F.Symbol] -> F.Symbol -> Bool
isSplSymbol env bs x
  =  isWiredInName x
  || elem x bs
  || S.member x (reGlobSyms env)

instance (Qualify a) => Qualify (Located a) where
  qualify env name l bs = fmap (qualify env name l bs)

instance (Qualify a) => Qualify [a] where
  qualify env name l bs = fmap (qualify env name l bs)

instance (Qualify a) => Qualify (Maybe a) where
  qualify env name l bs = fmap (qualify env name l bs)

instance Qualify Body where
  qualify env name l bs (P   p) = P   (qualify env name l bs p)
  qualify env name l bs (E   e) = E   (qualify env name l bs e)
  qualify env name l bs (R x p) = R x (qualify env name l bs p)

instance Qualify TyConInfo where
  qualify env name l bs tci = tci { sizeFunction = qualify env name l bs <$> sizeFunction tci }

instance Qualify RTyCon where
  qualify env name l bs rtc = rtc { rtc_info = qualify env name l bs (rtc_info rtc) }

instance Qualify (Measure SpecType Ghc.DataCon) where
  qualify env name _ bs m = m -- FIXME substEnv env name bs $
    { msName = qualify env name l bs     lname
    , msEqns = qualify env name l bs <$> msEqns m
    }
    where
      l      = F.loc  lname
      lname  = msName m


instance Qualify (Def ty ctor) where
  qualify env name l bs d = d
    { body  = qualify env name l (bs ++ bs') (body d) }
    where
      bs'   = fst <$> binds d

instance Qualify BareMeasure where
  qualify env name l bs m = m
    { msEqns = qualify env name l bs (msEqns m)
    }

instance Qualify DataCtor where
  qualify env name l bs c = c
    { dcTheta  = qualify env name l bs (dcTheta  c)
    , dcFields = qualify env name l bs (dcFields c)
    , dcResult = qualify env name l bs (dcResult c)
    }

instance Qualify DataDecl where
  qualify env name l bs d = d
    { tycDCons  = qualify env name l bs (tycDCons  d)
    , tycPropTy = qualify env name l bs (tycPropTy d)
    }

instance Qualify ModSpecs where
  qualify env name l bs = Misc.hashMapMapWithKey (\_ -> qualify env name l bs)

instance Qualify b => Qualify (a, b) where
  qualify env name l bs (x, y) = (x, qualify env name l bs y)

instance Qualify BareSpec where
  qualify = qualifyBareSpec

qualifyBareSpec :: Env -> ModName -> F.SourcePos -> [F.Symbol] -> BareSpec -> BareSpec
qualifyBareSpec env name l bs sp = sp
  { measures   = qualify env name l bs (measures   sp)
  , asmSigs    = qualify env name l bs (asmSigs    sp)
  , sigs       = qualify env name l bs (sigs       sp)
  , localSigs  = qualify env name l bs (localSigs  sp)
  , reflSigs   = qualify env name l bs (reflSigs   sp)
  , dataDecls  = qualify env name l bs (dataDecls  sp)
  , newtyDecls = qualify env name l bs (newtyDecls sp)
  , ialiases   = [ (f x, f y) | (x, y) <- ialiases sp ]
  }
  where f      = qualify env name l bs

instance Qualify a => Qualify (RTAlias F.Symbol a) where
  qualify env name l bs rtAlias
   = rtAlias { rtName  = qualify env name l bs (rtName rtAlias)
             , rtTArgs = qualify env name l bs (rtTArgs rtAlias)
             , rtVArgs = qualify env name l bs (rtVArgs rtAlias)
             , rtBody  = qualify env name l bs (rtBody rtAlias)
             }

instance Qualify F.Expr where
  qualify = substEnv

instance Qualify RReft where
  qualify = substEnv

instance Qualify F.Qualifier where
  qualify env name _ bs q = q { F.qBody = qualify env name (F.qPos q) bs' (F.qBody q) }
    where
      bs'                 = bs ++ (F.qpSym <$> F.qParams q)

substEnv :: (F.Subable a) => Env -> ModName -> F.SourcePos -> [F.Symbol] -> a -> a
substEnv env name l bs = F.substa (qualifySymbol env name l bs)

instance Qualify SpecType where
  qualify x1 x2 x3 x4 x5 = emapReft (substFreeEnv x1 x2 x3) x4 x5

instance Qualify BareType where
  qualify x1 x2 x3 x4 x5 = emapReft (substFreeEnv x1 x2 x3) x4 x5

substFreeEnv :: (F.Subable a) => Env -> ModName -> F.SourcePos -> [F.Symbol] -> a -> a
substFreeEnv env name l bs = F.substf (F.EVar . qualifySymbol env name l bs)

-------------------------------------------------------------------------------
lookupGhcNamedVar :: (Ghc.NamedThing a, F.Symbolic a) => Env -> ModName -> a -> Maybe Ghc.Var
-------------------------------------------------------------------------------
lookupGhcNamedVar env name z = maybeResolveSym  env name "Var" lx
  where
    lx                       = GM.namedLocSymbol z

lookupGhcVar :: Env -> ModName -> String -> LocSymbol -> Lookup Ghc.Var
lookupGhcVar env name kind lx = case resolveLocSym env name kind lx of
    Right v -> Mb.maybe (Right v) Right (lookupLocalVar env lx [v])
    Left  e -> Mb.maybe (Left  e) Right (lookupLocalVar env lx [])

  -- where
    -- err e   = Misc.errorP "error-lookupGhcVar" (F.showpp (e, F.loc lx, lx))
  --  err     = Ex.throw

-- | @lookupLocalVar@ takes as input the list of "global" (top-level) vars
--   that also match the name @lx@; we then pick the "closest" definition.
--   See tests/names/LocalSpec.hs for a motivating example.

lookupLocalVar :: Env -> LocSymbol -> [Ghc.Var] -> Maybe Ghc.Var
lookupLocalVar env lx gvs = Misc.findNearest lxn kvs
  where
    _msg                  = "LOOKUP-LOCAL: " ++ F.showpp (F.val lx, lxn, kvs)
    kvs                   = gs ++ M.lookupDefault [] x (reLocalVars env)
    gs                    = [(F.unPos (F.srcLine v), v) | v <- gvs]
    lxn                   = F.unPos (F.srcLine lx)
    (_, x)                = unQualifySymbol (F.val lx)

lookupGhcDataCon :: Env -> ModName -> String -> LocSymbol -> Lookup Ghc.DataCon
lookupGhcDataCon = resolveLocSym -- strictResolveSym

lookupGhcTyCon :: Env -> ModName -> String -> LocSymbol -> Lookup Ghc.TyCon
lookupGhcTyCon env name k lx = myTracepp ("LOOKUP-TYCON: " ++ F.showpp (val lx))
                               $ {- strictResolveSym -} resolveLocSym env name k lx

lookupGhcDnTyCon :: Env -> ModName -> String -> DataName -> Lookup (Maybe Ghc.TyCon)
-- lookupGhcDnTyCon = lookupGhcDnTyConE
lookupGhcDnTyCon env name msg = failMaybe env name . lookupGhcDnTyConE env name msg

lookupGhcDnTyConE :: Env -> ModName -> String -> DataName -> Lookup Ghc.TyCon
lookupGhcDnTyConE env name msg (DnCon  s)
  = lookupGhcDnCon env name msg s
lookupGhcDnTyConE env name msg (DnName s)
  = case resolveLocSym env name msg s of
      Right r -> Right r
      Left  e -> case lookupGhcDnCon  env name msg s of
                   Right r -> Right r
                   Left  _ -> Left  e


lookupGhcDnCon :: Env -> ModName -> String -> LocSymbol -> Lookup Ghc.TyCon
lookupGhcDnCon env name msg = fmap Ghc.dataConTyCon . resolveLocSym env name msg

-------------------------------------------------------------------------------
-- | Checking existence of names
-------------------------------------------------------------------------------
knownGhcType :: Env ->  ModName -> LocBareType -> Bool
knownGhcType env name (F.Loc l _ t) =
  case ofBareTypeE env name l Nothing t of
    Left e  -> myTracepp ("knownType: " ++ F.showpp (t, e)) False
    Right _ -> True



_rTypeTyCons :: (Ord c) => RType c tv r -> [c]
_rTypeTyCons        = Misc.sortNub . foldRType f []
  where
    f acc t@RApp {} = rt_tycon t : acc
    f acc _         = acc

-- Aargh. Silly that each of these is the SAME code, only difference is the type.

knownGhcVar :: Env -> ModName -> LocSymbol -> Bool
knownGhcVar env name lx = Mb.isJust v
  where
    v :: Maybe Ghc.Var -- This annotation is crucial
    v = myTracepp ("knownGhcVar " ++ F.showpp lx)
      $ maybeResolveSym env name "known-var" lx

knownGhcTyCon :: Env -> ModName -> LocSymbol -> Bool
knownGhcTyCon env name lx = myTracepp  msg $ Mb.isJust v
  where
    msg = "knownGhcTyCon: "  ++ F.showpp lx
    v :: Maybe Ghc.TyCon -- This annotation is crucial
    v = maybeResolveSym env name "known-tycon" lx

knownGhcDataCon :: Env -> ModName -> LocSymbol -> Bool
knownGhcDataCon env name lx = Mb.isJust v
  where
    v :: Maybe Ghc.DataCon -- This annotation is crucial
    v = myTracepp ("knownGhcDataCon" ++ F.showpp lx)
      $ maybeResolveSym env name "known-datacon" lx

-------------------------------------------------------------------------------
-- | Using the environment
-------------------------------------------------------------------------------
class ResolveSym a where
  resolveLocSym :: Env -> ModName -> String -> LocSymbol -> Lookup a

instance ResolveSym Ghc.Var where
  resolveLocSym = resolveWith "variable" $ \case
                    Ghc.AnId x -> Just x
                    _          -> Nothing

instance ResolveSym Ghc.TyCon where
  resolveLocSym = resolveWith "type constructor" $ \case
                    Ghc.ATyCon x -> Just x
                    _            -> Nothing

instance ResolveSym Ghc.DataCon where
  resolveLocSym = resolveWith "data constructor" $ \case
                    Ghc.AConLike (Ghc.RealDataCon x) -> Just x
                    _                                -> Nothing


{- Note [ResolveSym for Symbol]

In case we need to resolve (aka qualify) a 'Symbol', we need to do some extra work. Generally speaking,
all these 'ResolveSym' instances perform a lookup into a 'Map' keyed by the 'Symbol' in
order to find a 'TyThing'. More specifically such map is known as the 'TyThingMap':

type TyThingMap = M.HashMap F.Symbol [(F.Symbol, Ghc.TyThing)]

This means, in practice, that we might have more than one result indexed by a given 'Symbol', and we need
to make a choice. The function 'rankedThings' does this. By default, we try to extract only /identifiers/
(i.e. a GHC's 'Id') out of an input 'TyThing', but in the case of test \"T1688\", something different happened.
By tracing calls to 'rankedThings' (called by 'resolveLocSym') there were cases where we had something like
this as our input TyThingMap:

[
 1 : T1688Lib : Data constructor T1688Lib.Lambda,
 1 : T1688Lib : Identifier T1688Lib.Lambda
]

Here name resolution worked because 'resolveLocSym' used the 'ResolveSym' instance defined for 'GHC.Var' that
looks only for 'Id's (contained inside 'Identifier's, and we had one). In some other cases, though,
'resolveLocSym' got called with only this:

[1 : T1688Lib : Data constructor T1688Lib.Lambda]

This would /not/ yield a match, despite the fact a \"Data constructor\" in principle /does/ contain an 'Id'
(it can be extracted out of a 'RealDataCon' by calling 'dataConWorkId'). In the case of test T1688, such
failed lookup caused the 'Symbol' to /not/ qualify, which in turn caused the symbols inside the type synonym:

ProofOf( Step (App (Lambda x e) v) e)

To not qualify. Finally, by the time 'expand' was called, the 'ProofOf' type alias would be replaced with
the correct refinement, but the unqualified 'Symbol's would now cause a test failure when refining the client
module.

It's not clear to me (Alfredo) why 'resolveLocSym' is called multiple times within the same module with
different inputs, but it definitely makes sense to allow for the special case here, at least for 'Symbol's.

Probably finding the /root cause/ would entail partially rewriting the name resoultion engine.

-}


instance ResolveSym F.Symbol where
  resolveLocSym env name _ lx =
    -- If we can't resolve the input 'Symbol' from an 'Id', try again
    -- by grabbing the 'Id' of an 'AConLike', if any.
    -- See Note [ResolveSym for Symbol].
    let resolved =  resolveLocSym env name "Var" lx
                 <> resolveWith "variable" lookupVarInsideRealDataCon env name "Var" lx
    in case resolved of
      Left _               -> Right (val lx)
      Right (v :: Ghc.Var) -> Right (F.symbol v)
    where
      lookupVarInsideRealDataCon :: Ghc.TyThing -> Maybe Ghc.Var
      lookupVarInsideRealDataCon = \case
        Ghc.AConLike (Ghc.RealDataCon x) -> Just (Ghc.dataConWorkId x)
        _                                -> Nothing



resolveWith :: (PPrint a) => PJ.Doc -> (Ghc.TyThing -> Maybe a) -> Env -> ModName -> String -> LocSymbol
            -> Lookup a
resolveWith kind f env name str lx =
  -- case Mb.mapMaybe f things of
  case rankedThings f things of
    []  -> Left [errResolve kind str lx]
    [x] -> Right x
    xs  -> Left [ErrDupNames sp (pprint (F.val lx)) (pprint <$> xs)]
  where
    _xSym   = F.val lx
    sp      = GM.fSrcSpanSrcSpan (F.srcSpan lx)
    things  = myTracepp msg $ lookupTyThing env name lx
    msg     = "resolveWith: " ++ str ++ " " ++ F.showpp (val lx)


rankedThings :: (Misc.EqHash k) => (a -> Maybe b) -> [(k, a)] -> [b]
rankedThings f ias = case Misc.sortOn fst (Misc.groupList ibs) of
                       (_,ts):_ -> ts
                       []       -> []
  where
    ibs            = Mb.mapMaybe (\(k, x) -> (k,) <$> f x) ias

-------------------------------------------------------------------------------
-- | @lookupTyThing@ is the central place where we lookup the @Env@ to find
--   any @Ghc.TyThing@ that match that name. The code is a bit hairy as we
--   have various heuristics to approximiate how GHC resolves names. e.g.
--   see tests-names-pos-*.hs, esp. vector04.hs where we need the name `Vector`
--   to resolve to `Data.Vector.Vector` and not `Data.Vector.Generic.Base.Vector`...
-------------------------------------------------------------------------------
lookupTyThing :: Env -> ModName -> LocSymbol -> [((Int, F.Symbol), Ghc.TyThing)]
-------------------------------------------------------------------------------
lookupTyThing env mdname lsym = [ (k, t) | (k, ts) <- ordMatches, t <- ts]

  where
    ordMatches             = Misc.sortOn fst (Misc.groupList matches)
    matches                = myTracepp ("matches-" ++ msg)
                             [ ((k, m), t) | (m, t) <- lookupThings env x
                                           , k      <- myTracepp msg $ mm nameSym m mds ]
    msg                    = "lookupTyThing: " ++ F.showpp (lsym, x, mds)
    (x, mds)               = symbolModules env (F.val lsym)
    nameSym                = F.symbol mdname
    mm name m mods         = myTracepp ("matchMod: " ++ F.showpp (lsym, name, m, mods)) $
                               matchMod env name m mods

lookupThings :: Env -> F.Symbol -> [(F.Symbol, Ghc.TyThing)]
lookupThings env x = myTracepp ("lookupThings: " ++ F.showpp x)
                   $ Mb.fromMaybe [] $ get x `mplus` get (GM.stripParensSym x)
  where
    get z          = M.lookup z (_reTyThings env)

matchMod :: Env -> F.Symbol -> F.Symbol -> Maybe [F.Symbol] -> [Int]
matchMod env tgtName defName = go
  where
    go Nothing               -- Score UNQUALIFIED names
     | defName == tgtName = [0]                       -- prioritize names defined in *this* module
     | otherwise          = [matchImp env defName 1]  -- prioritize directly imported modules over
                                                      -- names coming from elsewhere, with a

    go (Just ms)             -- Score QUALIFIED names
     |  isEmptySymbol defName
     && ms == [tgtName]   = [0]                       -- local variable, see tests-names-pos-local00.hs
     | ms == [defName]    = [1]
     | isExt              = [matchImp env defName 2]  -- to allow matching re-exported names e.g. Data.Set.union for Data.Set.Internal.union
     | otherwise          = []
     where
       isExt              = any (`isParentModuleOf` defName) ms

-- | Returns 'True' if the 'Symbol' given as a first argument represents a parent module for the second.
--
-- >>> L.symbolic "Data.Text" `isParentModuleOf` L.symbolic "Data.Text.Internal"
-- True
--
-- Invariants:
--
-- * The empty 'Symbol' is always considered the module prefix of the second,
--   in compliance with 'isPrefixOfSym' (AND: why?)
-- * If the parent \"hierarchy\" is smaller than the children's one, this is clearly not a parent module.
isParentModuleOf :: F.Symbol -> F.Symbol -> Bool
isParentModuleOf parentModule childModule
  | isEmptySymbol parentModule = True
  | otherwise                  =
    length parentHierarchy <= length childHierarchy && all (uncurry (==)) (zip parentHierarchy childHierarchy)
  where
    parentHierarchy :: [T.Text]
    parentHierarchy = T.splitOn "." . F.symbolText $ parentModule

    childHierarchy :: [T.Text]
    childHierarchy = T.splitOn "." . F.symbolText $ childModule


symbolModules :: Env -> F.Symbol -> (F.Symbol, Maybe [F.Symbol])
symbolModules env s = (x, glerb <$> modMb)
  where
    (modMb, x)      = unQualifySymbol s
    glerb m         = M.lookupDefault [m] m qImps
    qImps           = qiNames (reQualImps env)

-- | @matchImp@ lets us prioritize @TyThing@ defined in directly imported modules over
--   those defined elsewhere. Specifically, in decreasing order of priority we have
--   TyThings that we:
--   * DIRECTLY     imported WITHOUT qualification
--   * TRANSITIVELY imported (e.g. were re-exported by SOME imported module)
--   * QUALIFIED    imported (so qualify the symbol to get this result!)

matchImp :: Env -> F.Symbol -> Int -> Int
matchImp env defName i
  | isUnqualImport = i
  | isQualImport   = i + 2
  | otherwise      = i + 1
  where
    isUnqualImport = S.member defName (reAllImps env) && not isQualImport
    isQualImport   = S.member defName (qiModules (reQualImps env))


-- | `unQualifySymbol name sym` splits `sym` into a pair `(mod, rest)` where
--   `mod` is the name of the module, derived from `sym` if qualified.
unQualifySymbol :: F.Symbol -> (Maybe F.Symbol, F.Symbol)
unQualifySymbol sym
  | GM.isQualifiedSym sym = Misc.mapFst Just (splitModuleNameExact sym)
  | otherwise             = (Nothing, sym)

splitModuleNameExact :: F.Symbol -> (F.Symbol, F.Symbol)
splitModuleNameExact x' = myTracepp ("splitModuleNameExact for " ++ F.showpp x)
                          (GM.takeModuleNames x, GM.dropModuleNames x)
  where
    x = GM.stripParensSym x'

errResolve :: PJ.Doc -> String -> LocSymbol -> Error
errResolve k msg lx = ErrResolve (GM.fSrcSpan lx) k (F.pprint (F.val lx)) (PJ.text msg)

-- -- | @strictResolve@ wraps the plain @resolve@ to throw an error
-- --   if the name being searched for is unknown.
-- strictResolveSym :: (ResolveSym a) => Env -> ModName -> String -> LocSymbol -> a
-- strictResolveSym env name kind x = case resolveLocSym env name kind x of
--   Left  err -> Misc.errorP "error-strictResolveSym" (F.showpp err)
--   Right val -> val

-- | @maybeResolve@ wraps the plain @resolve@ to return @Nothing@
--   if the name being searched for is unknown.
maybeResolveSym :: (ResolveSym a) => Env -> ModName -> String -> LocSymbol -> Maybe a
maybeResolveSym env name kind x = case resolveLocSym env name kind x of
  Left  _   -> Nothing
  Right val -> Just val

-------------------------------------------------------------------------------
-- | @ofBareType@ and @ofBareTypeE@ should be the _only_ @SpecType@ constructors
-------------------------------------------------------------------------------
ofBareType :: Env -> ModName -> F.SourcePos -> Maybe [PVar BSort] -> BareType -> SpecType
ofBareType env name l ps t = either fail' id (ofBareTypeE env name l ps t)
  where
    fail'                  = Ex.throw
    -- fail                   = Misc.errorP "error-ofBareType" . F.showpp

ofBareTypeE :: Env -> ModName -> F.SourcePos -> Maybe [PVar BSort] -> BareType -> Lookup SpecType
ofBareTypeE env name l ps t = ofBRType env name (resolveReft env name l ps t) l t

resolveReft :: Env -> ModName -> F.SourcePos -> Maybe [PVar BSort] -> BareType -> [F.Symbol] -> RReft -> RReft
resolveReft env name l ps t bs
        = qualify env name l bs
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

ofBSortE :: Env -> ModName -> F.SourcePos -> BSort -> Lookup RSort
ofBSortE env name l t = ofBRType env name (const id) l t

ofBPVar :: Env -> ModName -> F.SourcePos -> BPVar -> RPVar
ofBPVar env name l = fmap (ofBSort env name l)

--------------------------------------------------------------------------------
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
         -> Lookup (RRType r)
ofBRType env name f l = go []
  where
    goReft bs r             = return (f bs r)
    goRFun bs x i t1 t2 r  = RFun x i{permitTC = Just (typeclass (getConfig env))} <$> (rebind x <$> go bs t1) <*> go (x:bs) t2 <*> goReft bs r
    rebind x t              = F.subst1 t (x, F.EVar $ rTypeValueVar t)
    go bs (RAppTy t1 t2 r)  = RAppTy <$> go bs t1 <*> go bs t2 <*> goReft bs r
    go bs (RApp tc ts rs r) = goRApp bs tc ts rs r
    go bs (RFun x i t1 t2 r) = goRFun bs x i t1 t2 r
    go bs (RVar a r)        = RVar (RT.bareRTyVar a) <$> goReft bs r
    go bs (RAllT a t r)     = RAllT a' <$> go bs t <*> goReft bs r
      where a'              = dropTyVarInfo (mapTyVarValue RT.bareRTyVar a)
    go bs (RAllP a t)       = RAllP a' <$> go bs t
      where a'              = ofBPVar env name l a
    go bs (RAllE x t1 t2)   = RAllE x  <$> go bs t1    <*> go bs t2
    go bs (REx x t1 t2)     = REx   x  <$> go bs t1    <*> go (x:bs) t2
    go bs (RRTy xts r o t)  = RRTy  <$> xts' <*> goReft bs r <*> pure o <*> go bs t
      where xts'            = mapM (Misc.mapSndM (go bs)) xts
    go bs (RHole r)         = RHole    <$> goReft bs r
    go bs (RExprArg le)     = return    $ RExprArg (qualify env name l bs le)
    goRef bs (RProp ss (RHole r)) = rPropP <$> mapM goSyms ss <*> goReft bs r
    goRef bs (RProp ss t)         = RProp  <$> mapM goSyms ss <*> go bs t
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

matchTyCon :: Env -> ModName -> LocSymbol -> Int -> Lookup Ghc.TyCon
matchTyCon env name lc@(Loc _ _ c) arity
  | isList c && arity == 1  = Right Ghc.listTyCon
  | isTuple c               = Right tuplTc
  | otherwise               = resolveLocSym env name msg lc
  where
    msg                     = "matchTyCon: " ++ F.showpp c
    tuplTc                  = Ghc.tupleTyCon Ghc.Boxed arity


bareTCApp :: (Expandable r)
          => r
          -> Located Ghc.TyCon
          -> [RTProp RTyCon RTyVar r]
          -> [RType RTyCon RTyVar r]
          -> RType RTyCon RTyVar r
bareTCApp r (Loc l _ c) rs ts | Just rhs <- Ghc.synTyConRhs_maybe c
  = if GM.kindTCArity c < length ts
      then Ex.throw err -- error (F.showpp err)
      else tyApp (RT.subsTyVarsMeet su $ RT.ofType rhs) (drop nts ts) rs r
    where
       tvs = [ v | (v, b) <- zip (GM.tyConTyVarsDef c) (Ghc.tyConBinders c), GM.isAnonBinder b]
       su  = zipWith (\a t -> (RT.rTyVar a, toRSort t, t)) tvs ts
       nts = length tvs

       err :: Error
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
tyApp _                 _  _   _  = panic Nothing "Bare.Type.tyApp on invalid inputs"

expandRTypeSynonyms :: (Expandable r) => RRType r -> RRType r
expandRTypeSynonyms = RT.ofType . Ghc.expandTypeSynonyms . RT.toType False

{-
expandRTypeSynonyms :: (Expandable r) => RRType r -> RRType r
expandRTypeSynonyms t
  | rTypeHasHole t = t
  | otherwise      = expandRTypeSynonyms' t

rTypeHasHole :: RType c tv r -> Bool
rTypeHasHole = foldRType f False
  where
    f _ (RHole _) = True
    f b _         = b
-}

------------------------------------------------------------------------------------------
-- | Is this the SAME as addTyConInfo? No. `txRefSort`
-- (1) adds the _real_ sorts to RProp,
-- (2) gathers _extra_ RProp at turns them into refinements,
--     e.g. tests/pos/multi-pred-app-00.hs
------------------------------------------------------------------------------------------

txRefSort :: TyConMap -> F.TCEmb Ghc.TyCon -> LocSpecType -> LocSpecType
txRefSort tyi tce t = F.atLoc t $ mapBot (addSymSort (GM.fSrcSpan t) tce tyi) (val t)

addSymSort :: Ghc.SrcSpan -> F.TCEmb Ghc.TyCon -> TyConMap -> SpecType -> SpecType
addSymSort sp tce tyi (RApp rc@RTyCon{} ts rs rr)
  = RApp rc ts (zipWith3 (addSymSortRef sp rc) pvs rargs [1..]) r2
  where
    (_, pvs)           = RT.appRTyCon tce tyi rc ts
    -- pvs             = rTyConPVs rc'
    (rargs, rrest)     = splitAt (length pvs) rs
    r2                 = L.foldl' go rr rrest
    go r (RProp _ (RHole r')) = r' `F.meet` r
    go r (RProp  _ t' )       = let r' = Mb.fromMaybe mempty (stripRTypeBase t') in r `F.meet` r'

addSymSort _ _ _ t
  = t

addSymSortRef :: (PPrint s) => Ghc.SrcSpan -> s -> RPVar -> SpecProp -> Int -> SpecProp
addSymSortRef sp rc p r i
  | isPropPV p
  = addSymSortRef' sp rc i p r
  | otherwise
  = panic Nothing "addSymSortRef: malformed ref application"

addSymSortRef' :: (PPrint s) => Ghc.SrcSpan -> s -> Int -> RPVar -> SpecProp -> SpecProp
addSymSortRef' _ _ _ p (RProp s (RVar v r)) | isDummy v
  = RProp xs t
    where
      t  = ofRSort (pvType p) `RT.strengthen` r
      xs = spliceArgs "addSymSortRef 1" s p

addSymSortRef' sp rc i p (RProp _ (RHole r@(MkUReft _ (Pr [up]))))
  | length xs == length ts
  = RProp xts (RHole r)
  | otherwise
  = -- Misc.errorP "ZONK" $ F.showpp (rc, pname up, i, length xs, length ts)
    uError $ ErrPartPred sp (pprint rc) (pprint $ pname up) i (length xs) (length ts)
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
spliceArgs msg syms p = go (fst <$> syms) (pargs p)
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
resolveLocalBinds :: Env -> [(Ghc.Var, LocBareType, Maybe [Located F.Expr])]
                  -> [(Ghc.Var, LocBareType, Maybe [Located F.Expr])]
---------------------------------------------------------------------------------
resolveLocalBinds env xtes = [ (x,t,es) | (x, (t, es)) <- topTs ++ replace locTs ]
  where
    (locTs, topTs)         = partitionLocalBinds [ (x, (t, es)) | (x, t, es) <- xtes]
    replace                = M.toList . replaceSigs . M.fromList
    replaceSigs sigm       = coreVisitor replaceVisitor M.empty sigm cbs
    cbs                    = _giCbs (reSrc env)

replaceVisitor :: CoreVisitor SymMap SigMap
replaceVisitor = CoreVisitor
  { envF  = addBind
  , bindF = updSigMap
  , exprF = \_ m _ -> m
  }

addBind :: SymMap -> Ghc.Var -> SymMap
addBind env v = case localKey v of
  Just vx -> M.insert vx (F.symbol v) env
  Nothing -> env

updSigMap :: SymMap -> SigMap -> Ghc.Var -> SigMap
updSigMap env m v = case M.lookup v m of
  Nothing  -> m
  Just tes -> M.insert v (myTracepp ("UPD-LOCAL-SIG " ++ GM.showPpr v) $ renameLocalSig env tes) m

renameLocalSig :: SymMap -> (LocBareType, Maybe [Located F.Expr])
               -> (LocBareType, Maybe [Located F.Expr])
renameLocalSig env (t, es) = (F.substf tSub t, F.substf esSub es)
  where
    tSub                   = F.EVar . qualifySymMap env
    esSub                  = tSub `F.substfExcept` xs
    xs                     = ty_binds (toRTypeRep (F.val t))

qualifySymMap :: SymMap -> F.Symbol -> F.Symbol
qualifySymMap env x = M.lookupDefault x x env

type SigMap = M.HashMap Ghc.Var  (LocBareType, Maybe [Located F.Expr])
type SymMap = M.HashMap F.Symbol F.Symbol

---------------------------------------------------------------------------------
partitionLocalBinds :: [(Ghc.Var, a)] -> ([(Ghc.Var, a)], [(Ghc.Var, a)])
---------------------------------------------------------------------------------
partitionLocalBinds = L.partition (Mb.isJust . localKey . fst)
