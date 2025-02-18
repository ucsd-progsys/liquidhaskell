-- | This module has the code that uses the GHC definitions to:
--   1. MAKE a name-resolution environment,
--   2. USE the environment to translate plain symbols into Var, TyCon, etc.

{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TupleSections         #-}

module Language.Haskell.Liquid.Bare.Resolve
  ( -- * Creating the Environment
    makeEnv
  , makeLocalVars
  , makeGHCTyLookupEnv
  , GHCTyLookupEnv(..)

    -- * Resolving symbols
  , Lookup

  -- * Looking up names
  , lookupGhcDataConLHName
  , lookupGhcDnTyCon
  , lookupGhcIdLHName
  , lookupLocalVar
  , lookupGhcTyConLHName
  , lookupGhcTyThingFromName
  , lookupGhcId

  -- * Checking if names exist
  , knownGhcType

  -- * Misc
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
import           Data.Bifunctor (first)
import           Data.Function (on)
import           Data.IORef (newIORef)
import qualified Data.List                         as L
import qualified Data.HashSet                      as S
import qualified Data.Maybe                        as Mb
import qualified Data.HashMap.Strict               as M
import           GHC.Stack
import           Text.Megaparsec.Pos (sourceColumn, sourceLine)
import qualified Text.PrettyPrint.HughesPJ         as PJ

import qualified Language.Fixpoint.Types               as F
import qualified Language.Fixpoint.Types.Visitor       as F
import qualified Language.Fixpoint.Misc                as Misc
import qualified Liquid.GHC.API       as Ghc
import qualified Language.Haskell.Liquid.GHC.Interface as Interface
import qualified Language.Haskell.Liquid.GHC.Misc      as GM
import qualified Language.Haskell.Liquid.Misc          as Misc
import           Language.Haskell.Liquid.Types.DataDecl
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import qualified Language.Haskell.Liquid.Types.RefType as RT
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Visitors
import           Language.Haskell.Liquid.Bare.Types
import           Language.Haskell.Liquid.UX.Config
import           System.IO.Unsafe (unsafePerformIO)

myTracepp :: (F.PPrint a) => String -> a -> a
myTracepp = F.notracepp

-- type Lookup a = Misc.Validate [Error] a
type Lookup a = Either [Error] a

-------------------------------------------------------------------------------
-- | Creating an environment
-------------------------------------------------------------------------------
makeEnv :: Config -> GHCTyLookupEnv -> [Ghc.Id] -> Ghc.TcGblEnv -> Ghc.InstEnvs -> LocalVars -> GhcSrc -> LogicMap -> [(ModName, BareSpec)] -> Env
makeEnv cfg ghcTyLookupEnv dataConIds tcg instEnv localVars src lmap specs = RE
  { reTyLookupEnv = ghcTyLookupEnv
  , reTcGblEnv  = tcg
  , reInstEnvs = instEnv
  , reUsedExternals = usedExternals
  , reLMap      = lmap
  , reDataConIds = dataConIds
  , reLocalVars = localVars
  , reSrc       = src
  , reGlobSyms  = S.fromList     globalSyms
  , reCfg       = cfg
  }
  where
    globalSyms  = concatMap getGlobalSyms specs
    usedExternals = Ghc.exprsOrphNames $ map snd $ Ghc.flattenBinds $ _giCbs src

getGlobalSyms :: (ModName, BareSpec) -> [F.Symbol]
getGlobalSyms (_, spec)
  = filter (not . GM.isQualifiedSym)
       $ (mbName <$> measures  spec)
      ++ (mbName <$> cmeasures spec)
      ++ (mbName <$> imeasures spec)
      ++ (mbName <$> omeasures spec)
  where
    mbName = lhNameToResolvedSymbol . F.val . msName

makeLocalVars :: [Ghc.CoreBind] -> LocalVars
makeLocalVars = localVarMap . localBinds

-- TODO: rewrite using CoreVisitor
localBinds :: [Ghc.CoreBind] -> [LocalVarDetails]
localBinds                    = concatMap (bgoT [])
  where
    bgoT g (Ghc.NonRec _ e) = go g e
    bgoT g (Ghc.Rec xes)    = concatMap (go g . snd) xes
    pgo g isRec (x, e)      = mkLocalVarDetails g isRec x : go g e
    bgo g (Ghc.NonRec x e)  = pgo g False (x, e)
    bgo g (Ghc.Rec xes)     = concatMap (pgo g True) xes
    go g (Ghc.App e a)       = concatMap (go g) [e, a]
    go g (Ghc.Lam x e)       = go (x:g) e
    go g (Ghc.Let b e)       = bgo g b ++ go (Ghc.bindersOf b ++ g) e
    go g (Ghc.Tick _ e)      = go g e
    go g (Ghc.Cast e _)      = go g e
    go g (Ghc.Case e _ _ cs) = go g e ++ concatMap (\(Ghc.Alt _ bs e') -> go (bs ++ g) e') cs
    go _ (Ghc.Var _)         = []
    go _ _                   = []

    mkLocalVarDetails g isRec v = LocalVarDetails
      { lvdSourcePos = F.sp_start $ F.srcSpan v
      , lvdVar = v
      , lvdLclEnv = g
      , lvdIsRec = isRec
      }

localVarMap :: [LocalVarDetails] -> LocalVars
localVarMap lvds =
    LocalVars
      { lvSymbols = Misc.group
          [ (x, lvd)
          | lvd <- lvds
          , let v = lvdVar lvd
                x = F.symbol $ Ghc.occNameString $ Ghc.nameOccName $ Ghc.varName v
          ]
      , lvNames = Ghc.mkNameEnvWith (Ghc.getName . lvdVar) lvds
      }

makeGHCTyLookupEnv :: Ghc.CoreProgram -> Ghc.TcRn GHCTyLookupEnv
makeGHCTyLookupEnv cbs = do
    hscEnv <- Ghc.getTopEnv
    session <- Ghc.Session <$> Ghc.liftIO (newIORef hscEnv)
    tcg <- Ghc.getGblEnv
      -- Types differ in tcg_type_env vs the core bindings though they seem to
      -- be alpha-equivalent. We prefer the type in the core bindings and we
      -- also include the types of local variables.
    let varsEnv = Ghc.mkTypeEnv $ map Ghc.AnId $ letVars cbs
        typeEnv = Ghc.tcg_type_env tcg `Ghc.plusTypeEnv` varsEnv
    return GHCTyLookupEnv
      { gtleSession = session
      , gtleTypeEnv = typeEnv
      }

localKey   :: Ghc.Var -> Maybe F.Symbol
localKey v
  | isLocal m = Just x
  | otherwise = Nothing
  where
    (m, x)    = splitModuleNameExact . GM.dropModuleUnique . F.symbol $ v

isLocal :: F.Symbol -> Bool
isLocal = isEmptySymbol

isEmptySymbol :: F.Symbol -> Bool
isEmptySymbol x = F.lengthSym x == 0

-- | @lookupLocalVar@ takes as input the list of "global" (top-level) vars
--   that also match the name @lx@; we then pick the "closest" definition.
--   See tests/names/LocalSpec.hs for a motivating example.

lookupLocalVar :: F.Loc a => LocalVars -> LocSymbol -> [a] -> Maybe (Either a Ghc.Var)
lookupLocalVar localVars lx gvs = findNearest lxn kvs
  where
    kvs                   = prioritizeRecBinds (M.lookupDefault [] x (lvSymbols localVars)) ++ gs
    gs                    = [(F.sp_start $ F.srcSpan v, Left v) | v <- gvs]
    lxn                   = F.sp_start $ F.srcSpan lx
    (_, x)                = unQualifySymbol (F.val lx)

    -- Sometimes GHC produces multiple bindings that have the same source
    -- location. To select among these, we give preference to the recursive
    -- bindings which might need termination metrics.
    prioritizeRecBinds lvds =
      let (recs, nrecs) = L.partition lvdIsRec lvds
       in map lvdToPair (recs ++ nrecs)
    lvdToPair lvd = (lvdSourcePos lvd, Right (lvdVar lvd))

    findNearest :: F.SourcePos -> [(F.SourcePos, b)] -> Maybe b
    findNearest key kvs1 = argMin [ (posDistance key k, v) | (k, v) <- kvs1 ]

    -- We prefer the var with the smaller distance, or equal distance
    -- but left of the spec, or not left of the spec but below it.
    posDistance a b =
      ( abs (F.unPos (sourceLine a) - F.unPos (sourceLine b))
      , sourceColumn a < sourceColumn b -- Note: False is prefered/smaller to True
      , sourceLine a > sourceLine b
      )

    argMin :: (Ord k) => [(k, v)] -> Maybe v
    argMin = Mb.listToMaybe . map snd . L.sortBy (compare `on` fst)


lookupGhcDnTyCon :: Env -> ModName -> DataName -> Lookup (Maybe Ghc.TyCon)
lookupGhcDnTyCon env name = failMaybe env name . lookupGhcDnTyConE env

lookupGhcDnTyConE :: Env -> DataName -> Lookup Ghc.TyCon
lookupGhcDnTyConE env (DnCon  lname)
  = Ghc.dataConTyCon <$> lookupGhcDataConLHName env lname
lookupGhcDnTyConE env (DnName lname)
  = do
   case lookupTyThing (reTyLookupEnv env) lname of
     Ghc.ATyCon tc -> Right tc
     Ghc.AConLike (Ghc.RealDataCon d) -> Right $ Ghc.dataConTyCon d
     _ -> panic
           (Just $ GM.fSrcSpan lname) $ "not a type or data constructor: " ++ show (val lname)

lookupGhcDataConLHName :: HasCallStack => Env -> Located LHName -> Lookup Ghc.DataCon
lookupGhcDataConLHName env lname = do
   case lookupTyThing (reTyLookupEnv env) lname of
     Ghc.AConLike (Ghc.RealDataCon d) -> Right d
     _ -> panic
           (Just $ GM.fSrcSpan lname) $ "not a data constructor: " ++ show (val lname)

lookupGhcIdLHName :: HasCallStack => Env -> Located LHName -> Lookup Ghc.Id
lookupGhcIdLHName env lname =
   case lookupTyThing (reTyLookupEnv env) lname of
     Ghc.AConLike (Ghc.RealDataCon d) -> Right (Ghc.dataConWorkId d)
     Ghc.AnId x -> Right x
     _ -> panic
           (Just $ GM.fSrcSpan lname) $ "not a variable or data constructor: " ++ show (val lname)

lookupGhcTyThingFromName :: GHCTyLookupEnv -> Ghc.Name -> Maybe Ghc.TyThing
-- see note about unsafePerformIO in lookupTyThingMaybe
lookupGhcTyThingFromName env n =
   unsafePerformIO $ Ghc.reflectGhc (Interface.lookupTyThing (gtleTypeEnv env) n) (gtleSession env)

lookupGhcId :: Env -> Ghc.Name -> Maybe Ghc.Id
lookupGhcId env n =
    case lookupGhcTyThingFromName env' n of
      Just (Ghc.AConLike (Ghc.RealDataCon d)) -> Just (Ghc.dataConWorkId d)
      Just (Ghc.AnId x) -> Just x
      _ -> Nothing
  where
    env' = reTyLookupEnv env

-------------------------------------------------------------------------------
-- | Checking existence of names
-------------------------------------------------------------------------------
knownGhcType :: Env -> LocBareType -> Bool
knownGhcType env (F.Loc l _ t) =
  case ofBareTypeE env l Nothing t of
    Left e  -> myTracepp ("knownType: " ++ F.showpp (t, e)) False
    Right _ -> True



_rTypeTyCons :: (Ord c) => RType c tv r -> [c]
_rTypeTyCons        = Misc.sortNub . foldRType f []
  where
    f acc t@RApp {} = rt_tycon t : acc
    f acc _         = acc

-- | `unQualifySymbol name sym` splits `sym` into a pair `(mod, rest)` where
--   `mod` is the name of the module, derived from `sym` if qualified.
unQualifySymbol :: F.Symbol -> (Maybe F.Symbol, F.Symbol)
unQualifySymbol sym
  | GM.isQualifiedSym sym = first Just (splitModuleNameExact sym)
  | otherwise             = (Nothing, sym)

splitModuleNameExact :: F.Symbol -> (F.Symbol, F.Symbol)
splitModuleNameExact x' = myTracepp ("splitModuleNameExact for " ++ F.showpp x)
                          (GM.takeModuleNames x, GM.dropModuleNames x)
  where
    x = GM.stripParensSym x'

errResolve :: PJ.Doc -> String -> LocSymbol -> Error
errResolve k msg lx = ErrResolve (GM.fSrcSpan lx) k (F.pprint (F.val lx)) (PJ.text msg)

-------------------------------------------------------------------------------
-- | @ofBareType@ and @ofBareTypeE@ should be the _only_ @SpecType@ constructors
-------------------------------------------------------------------------------
ofBareType :: HasCallStack => Env -> F.SourcePos -> Maybe [PVar BSort] -> BareType -> SpecType
ofBareType env l ps t = either fail' id (ofBareTypeE env l ps t)
  where
    fail'                  = Ex.throw
    -- fail                   = Misc.errorP "error-ofBareType" . F.showpp

ofBareTypeE :: HasCallStack => Env -> F.SourcePos -> Maybe [PVar BSort] -> BareType -> Lookup SpecType
ofBareTypeE env l ps t = ofBRType env (const (resolveReft l ps t)) l t

resolveReft :: F.SourcePos -> Maybe [PVar BSort] -> BareType -> RReft -> RReft
resolveReft l ps t
        = txParam l RT.subvUReft (RT.uPVar <$> πs) t
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


ofBSort :: HasCallStack => Env -> F.SourcePos -> BSort -> RSort
ofBSort env l t = either (Misc.errorP "error-ofBSort" . F.showpp) id (ofBSortE env l t)

ofBSortE :: HasCallStack => Env -> F.SourcePos -> BSort -> Lookup RSort
ofBSortE env l t = ofBRType env (const id) l t

ofBPVar :: Env -> F.SourcePos -> BPVar -> RPVar
ofBPVar env l = fmap (ofBSort env l)

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
                    , Reftable r
                    , SubsTy RTyVar (RType RTyCon RTyVar ()) r
                    , Reftable (RTProp RTyCon RTyVar r)
                    , HasCallStack)

ofBRType :: (Expandable r) => Env -> ([F.Symbol] -> r -> r) -> F.SourcePos -> BRType r
         -> Lookup (RRType r)
ofBRType env f l = go []
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
      where a'              = ofBPVar env l a
    go bs (RAllE x t1 t2)   = RAllE x  <$> go bs t1    <*> go bs t2
    go bs (REx x t1 t2)     = REx   x  <$> go bs t1    <*> go (x:bs) t2
    go bs (RRTy xts r o t)  = RRTy  <$> xts' <*> goReft bs r <*> pure o <*> go bs t
      where xts'            = mapM (traverse (go bs)) xts
    go bs (RHole r)         = RHole    <$> goReft bs r
    go _ (RExprArg le)      = return    $ RExprArg le
    goRef bs (RProp ss (RHole r)) = rPropP <$> mapM goSyms ss <*> goReft bs r
    goRef bs (RProp ss t)         = RProp  <$> mapM goSyms ss <*> go bs t
    goSyms (x, t)                 = (x,) <$> ofBSortE env l t
    goRApp bs tc ts rs r          = bareTCApp <$> goReft bs r <*> lc' <*> mapM (goRef bs) rs <*> mapM (go bs) ts
      where
        lc'                    = F.atLoc lc <$> lookupGhcTyConLHName (reTyLookupEnv env) lc
        lc                     = btc_tc tc

lookupGhcTyConLHName :: HasCallStack => GHCTyLookupEnv -> Located LHName -> Lookup Ghc.TyCon
lookupGhcTyConLHName env lc = do
    case lookupTyThing env lc of
      Ghc.ATyCon tc -> Right tc
      Ghc.AConLike (Ghc.RealDataCon dc) -> Right $ Ghc.promoteDataCon dc
      _ -> panic
            (Just $ GM.fSrcSpan lc) $ "not a type constructor: " ++ show (val lc)

-- | Get the TyThing from an LHName.
--
-- This function uses 'unsafePerformIO' to lookup the 'Ghc.TyThing' of a 'Ghc.Name'.
-- This should be benign because the result doesn't depend of when exactly this is
-- called. Since this code is intended to be used inside a GHC plugin, there is no
-- danger that GHC is finalized before the result is evaluated.
lookupTyThingMaybe :: HasCallStack => GHCTyLookupEnv -> Located LHName -> Maybe Ghc.TyThing
lookupTyThingMaybe env lc@(Loc _ _ c0) = unsafePerformIO $ do
    case c0 of
      LHNUnresolved _ _ -> panic (Just $ GM.fSrcSpan lc) $ "unresolved name: " ++ show c0
      LHNResolved rn _ -> case rn of
        LHRLocal _ -> panic (Just $ GM.fSrcSpan lc) $ "cannot resolve a local name: " ++ show c0
        LHRIndex i -> panic (Just $ GM.fSrcSpan lc) $ "cannot resolve a LHRIndex " ++ show i
        LHRLogic _ -> panic (Just $ GM.fSrcSpan lc) $ "lookupTyThing: cannot resolve a LHRLogic name " ++ show (lhNameToResolvedSymbol c0)
        LHRGHC n ->
          Ghc.reflectGhc (Interface.lookupTyThing (gtleTypeEnv env) n) (gtleSession env)

lookupTyThing :: HasCallStack => GHCTyLookupEnv -> Located LHName -> Ghc.TyThing
lookupTyThing env lc =
    Mb.fromMaybe (panic (Just $ GM.fSrcSpan lc) $ "not found: " ++ show (val lc)) $
      lookupTyThingMaybe env lc

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


tyApp :: Reftable r => RType c tv r -> [RType c tv r] -> [RTProp c tv r] -> r
      -> RType c tv r
tyApp (RApp c ts rs r) ts' rs' r' = RApp c (ts ++ ts') (rs ++ rs') (r `meet` r')
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
    go r (RProp _ (RHole r')) = r' `meet` r
    go r (RProp  _ t' )       = let r' = Mb.fromMaybe mempty (stripRTypeBase t') in r `meet` r'

addSymSort _ _ _ t
  = t

addSymSortRef :: (PPrint s) => Ghc.SrcSpan -> s -> RPVar -> SpecProp -> Int -> SpecProp
addSymSortRef sp rc p r i = addSymSortRef' sp rc i p r

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
