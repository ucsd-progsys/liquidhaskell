{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Language.Haskell.Liquid.Bare.DataType
  ( dataConMap

  -- * Names for accessing Data Constuctors 
  , makeDataConChecker
  , makeDataConSelector
  , addClassEmbeds

  -- * Constructors
  , makeDataDecls
  , makeConTypes
  , makeRecordSelectorSigs
  , meetDataConSpec
  -- , makeTyConEmbeds

  , dataDeclSize
  ) where

import qualified Control.Exception                      as Ex
import           Control.Monad.Reader
import qualified Data.List                              as L
import qualified Data.HashMap.Strict                    as M
import qualified Data.HashSet                           as S
import qualified Data.Maybe                             as Mb

import qualified Language.Fixpoint.Types                as F
import qualified Liquid.GHC.Misc       as GM
import qualified Liquid.GHC.API        as Ghc
import           Language.Haskell.Liquid.Types.PredType (dataConPSpecType)
import qualified Language.Haskell.Liquid.Types.RefType  as RT
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Meet
import qualified Language.Fixpoint.Misc                 as Misc
import qualified Language.Haskell.Liquid.Misc           as Misc
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.WiredIn
import           Language.Haskell.Liquid.Types.Names (selfSymbol)

import qualified Language.Haskell.Liquid.Measure        as Ms

import qualified Language.Haskell.Liquid.Bare.Types     as Bare
import qualified Language.Haskell.Liquid.Bare.Resolve   as Bare
import           Text.Printf                     (printf)
import Text.PrettyPrint ((<+>))

--------------------------------------------------------------------------------
-- | 'DataConMap' stores the names of those ctor-fields that have been declared
--   as SMT ADTs so we don't make up new names for them.
--------------------------------------------------------------------------------
dataConMap :: [F.DataDecl] -> Bare.DataConMap
dataConMap ds = M.fromList $ do
  d     <- ds
  c     <- F.ddCtors d
  let fs = F.symbol <$> F.dcFields c
  zip ((F.symbol c,) <$> [1..]) fs


--------------------------------------------------------------------------------
-- | 'makeDataConChecker d' creates the measure for `is$d` which tests whether
--   a given value was created by 'd'. e.g. is$Nil or is$Cons.
--------------------------------------------------------------------------------
makeDataConChecker :: Ghc.DataCon -> F.Symbol
--------------------------------------------------------------------------------
makeDataConChecker = F.testSymbol . F.symbol

--------------------------------------------------------------------------------
-- | 'makeDataConSelector d' creates the selector `select$d$i`
--   which projects the i-th field of a constructed value.
--   e.g. `select$Cons$1` and `select$Cons$2` are respectively
--   equivalent to `head` and `tail`.
--------------------------------------------------------------------------------
makeDataConSelector :: Maybe Bare.DataConMap -> Ghc.DataCon -> Int -> F.Symbol
makeDataConSelector dmMb d i = M.lookupDefault def (F.symbol d, i) dm
  where
    dm                       = Mb.fromMaybe M.empty dmMb
    def                      = makeDataConSelector' d i


makeDataConSelector' :: Ghc.DataCon -> Int -> F.Symbol
makeDataConSelector' d i
  = symbolMeasure "$select" (dcSymbol d) (Just i)

dcSymbol :: Ghc.DataCon -> F.Symbol
dcSymbol = {- simpleSymbolVar -} F.symbol . Ghc.dataConWorkId

symbolMeasure :: String -> F.Symbol -> Maybe Int -> F.Symbol
symbolMeasure f d iMb = foldr1 F.suffixSymbol (dcPrefix : F.symbol f : d : rest)
  where
    rest          = maybe [] (Misc.single . F.symbol . show) iMb


--------------------------------------------------------------------------------
-- | makeClassEmbeds: sort-embeddings for numeric, and family-instance tycons
--------------------------------------------------------------------------------
addClassEmbeds :: Maybe [Ghc.ClsInst] -> [Ghc.TyCon] -> F.TCEmb Ghc.TyCon
               -> F.TCEmb Ghc.TyCon
addClassEmbeds instenv fiTcs = makeFamInstEmbeds fiTcs . makeNumEmbeds instenv

--------------------------------------------------------------------------------
-- | makeFamInstEmbeds : embed family instance tycons, see [NOTE:FamInstEmbeds]
--------------------------------------------------------------------------------
--     Query.R$58$EntityFieldBlobdog
--   with the actual family instance  types that have numeric instances as int [Check!]
--------------------------------------------------------------------------------
makeFamInstEmbeds :: [Ghc.TyCon] -> F.TCEmb Ghc.TyCon -> F.TCEmb Ghc.TyCon
makeFamInstEmbeds cs0 embeds = L.foldl' embed embeds famInstSorts
  where
    famInstSorts          = F.notracepp "famInstTcs"
                            [ (c, RT.typeSort embeds ty)
                                | c   <- cs
                                , ty  <- Mb.maybeToList (RT.famInstTyConType c) ]
    embed embs (c, t)     = F.tceInsert c t F.NoArgs embs
    cs                    = F.notracepp "famInstTcs-all" cs0

{- 
famInstTyConType :: Ghc.TyCon -> Maybe Ghc.Type
famInstTyConType c = case Ghc.tyConFamInst_maybe c of
    Just (c', ts) -> F.tracepp ("famInstTyConType: " ++ F.showpp (c, Ghc.tyConArity c, ts)) 
                     $ Just (famInstType (Ghc.tyConArity c) c' ts)
    Nothing       -> Nothing

famInstType :: Int -> Ghc.TyCon -> [Ghc.Type] -> Ghc.Type
famInstType n c ts = Ghc.mkTyConApp c (take (length ts - n) ts)
-}

{- | [NOTE:FamInstEmbeds] GHC represents family instances in two ways: 

     (1) As an applied type, 
     (2) As a special tycon.
     
     For example, consider `tests/pos/ExactGADT4.hs`:

        class PersistEntity record where
          data EntityField record :: * -> *

        data Blob = B { xVal :: Int, yVal :: Int }

        instance PersistEntity Blob where
           data EntityField Blob dog where
             BlobXVal :: EntityField Blob Int
             BlobYVal :: EntityField Blob Int

     here, the type of the constructor `BlobXVal` can be represented as:

     (1) EntityField Blob Int,

     or

     (2) R$58$EntityFieldBlobdog Int

     PROBLEM: For various reasons, GHC will use _both_ representations interchangeably,
     which messes up our sort-checker.

     SOLUTION: To address the above, we create an "embedding"

        R$58$EntityFieldBlobdog :-> EntityField Blob

     So that all occurrences of the (2) are treated as (1) by the sort checker.

 -}

--------------------------------------------------------------------------------
-- | makeNumEmbeds: embed types that have numeric instances as int [Check!]
--------------------------------------------------------------------------------
makeNumEmbeds :: Maybe [Ghc.ClsInst] -> F.TCEmb Ghc.TyCon -> F.TCEmb Ghc.TyCon
makeNumEmbeds Nothing x   = x
makeNumEmbeds (Just is) x = L.foldl' makeNumericInfoOne x is

makeNumericInfoOne :: F.TCEmb Ghc.TyCon -> Ghc.ClsInst -> F.TCEmb Ghc.TyCon
makeNumericInfoOne m is
  | isFracCls cls, Just tc <- instanceTyCon is
  = F.tceInsertWith (flip mappendSortFTC) tc (ftc tc True True) F.NoArgs m
  | isNumCls  cls, Just tc <- instanceTyCon is
  = F.tceInsertWith (flip mappendSortFTC) tc (ftc tc True False) F.NoArgs m
  | otherwise
  = m
  where
    cls         = Ghc.classTyCon (Ghc.is_cls is)
    ftc c f1 f2 = F.FTC (F.symbolNumInfoFTyCon (dummyLoc $ RT.tyConName c) f1 f2)

mappendSortFTC :: F.Sort -> F.Sort -> F.Sort
mappendSortFTC (F.FTC x) (F.FTC y) = F.FTC (F.mappendFTC x y)
mappendSortFTC s         (F.FTC _) = s
mappendSortFTC (F.FTC _) s         = s
mappendSortFTC s1        s2        = panic Nothing ("mappendSortFTC: s1 = " ++ showpp s1 ++ " s2 = " ++ showpp s2)

instanceTyCon :: Ghc.ClsInst -> Maybe Ghc.TyCon
instanceTyCon = go . Ghc.is_tys
  where
    go [Ghc.TyConApp c _] = Just c
    go _                  = Nothing

--------------------------------------------------------------------------------
-- | Create Fixpoint DataDecl from LH DataDecls --------------------------------
--------------------------------------------------------------------------------

-- | A 'DataPropDecl' is associated with a (`TyCon` and) `DataDecl`, and defines the
--   sort of relation that is established by terms of the given `TyCon`.
--   A 'DataPropDecl' say, 'pd' is associated with a 'dd' of type 'DataDecl' when
--   'pd' is the `SpecType` version of the `BareType` given by `tycPropTy dd`.

type DataPropDecl = (DataDecl, Maybe SpecType)

makeDataDecls :: Config -> F.TCEmb Ghc.TyCon -> ModName
              -> [(ModName, Ghc.TyCon, DataPropDecl)]
              -> [Located DataConP]
              -> (Diagnostics, [F.DataDecl])
makeDataDecls cfg tce name tds ds
  | makeDecls        = (mkDiagnostics warns [], okDecs)
  | otherwise        = (mempty, [])
  where
    makeDecls        = exactDCFlag cfg && not (noADT cfg)
    warns            = (mkWarnDecl . fst . fst . snd <$> badTcs) ++ (mkWarnDecl <$> badDecs)
    tds'             = resolveTyCons name tds
    tcDds            = filter ((/= Ghc.listTyCon) . fst)
                     $ groupDataCons tds' ds
    (okTcs, badTcs)  = L.partition isVanillaTc tcDds
    decs             = [ makeFDataDecls tce tc dd ctors | (tc, (dd, ctors)) <- okTcs]
    (okDecs,badDecs) = checkRegularData decs

isVanillaTc :: (a, (b, [(Ghc.DataCon, c)])) -> Bool
isVanillaTc (_, (_, ctors)) = all (Ghc.isVanillaDataCon . fst) ctors

checkRegularData :: [F.DataDecl] -> ([F.DataDecl], [F.DataDecl])
checkRegularData ds = (oks, badDs)
  where
    badDs           = F.checkRegular ds
    badSyms         = {- F.notracepp "BAD-Data" . -} S.fromList . fmap F.symbol $ badDs
    oks             = [ d |  d <- ds, not (S.member (F.symbol d) badSyms) ]

mkWarnDecl :: (F.Loc a, F.Symbolic a) => a -> Warning
mkWarnDecl d = mkWarning (GM.fSrcSpan d) ("Non-regular data declaration" <+> pprint (F.symbol d))


-- [NOTE:Orphan-TyCons]

{- | 'resolveTyCons' will prune duplicate 'TyCon' definitions, as follows:

      Let the "home" of a 'TyCon' be the module where it is defined.
      There are three kinds of 'DataDecl' definitions:

      1. A  "home"-definition is one that belongs to its home module,
      2. An "orphan"-definition is one that belongs to some non-home module.

      A 'DataUser' definition MUST be a "home" definition
          - otherwise you can avoid importing the definition
            and hence, unsafely pass its invariants!

      So, 'resolveTyConDecls' implements the following protocol:

      (a) If there is a "Home" definition,
          then use it, and IGNORE others.

      (b) If there are ONLY "orphan" definitions,
          then pick the one from module being analyzed.

      We COULD relax to allow for exactly one orphan `DataUser` definition
      which is the one that should be selected, but that seems like a
      slippery slope, as you can avoid importing the definition
      and hence, unsafely pass its invariants! (Feature not bug?)

-}
resolveTyCons :: ModName -> [(ModName, Ghc.TyCon, DataPropDecl)]
              -> [(Ghc.TyCon, (ModName, DataPropDecl))]
resolveTyCons mn mtds = [(tc, (m, d)) | (tc, mds) <- M.toList tcDecls
                                      , (m, d)    <- Mb.maybeToList $ resolveDecls mn tc mds ]
  where
    tcDecls          = Misc.group [ (tc, (m, d)) | (m, tc, d) <- mtds ]

-- | See [NOTE:Orphan-TyCons], the below function tells us which of (possibly many)
--   DataDecls to use.
resolveDecls :: ModName -> Ghc.TyCon -> Misc.ListNE (ModName, DataPropDecl)
             -> Maybe (ModName, DataPropDecl)
resolveDecls mName tc mds  = F.notracepp msg $
    case filter isHomeDef mds of
      x:_ -> Just x
      _ -> case filter isLHAssumptionsDef mds of
        [x] -> Just x
        xs@(_:_) -> error $
          "Multiple spec declarations of " ++ show (F.symbol tc) ++
          " found in _LHAssumption modules: " ++ show (map fst xs) ++
          ". Please, remove some of them."
        [] -> L.find isMyDef mds
  where
    msg                    = "resolveDecls" ++ F.showpp (mName, tc)
    isMyDef                = (mName ==)             . fst
    isHomeDef              = (tcHome ==) . F.symbol . fst
    tcHome                 = GM.takeModuleNames (F.symbol tc)
    isLHAssumptionsDef     = L.isSuffixOf "_LHAssumptions" . Ghc.moduleNameString . getModName . fst

groupDataCons :: [(Ghc.TyCon, (ModName, DataPropDecl))]
              -> [Located DataConP]
              -> [(Ghc.TyCon, (DataPropDecl, [(Ghc.DataCon, DataConP)]))]
groupDataCons tds ds = [ (tc, (d, dds')) | (tc, ((m, d), dds)) <- tcDataCons
                                         , let dds' = filter (isResolvedDataConP m . snd) dds
                       ]
  where
    tcDataCons       = M.toList $ M.intersectionWith (,) declM ctorM
    declM            = M.fromList tds
    ctorM            = Misc.group [(Ghc.dataConTyCon d, (d, dcp)) | Loc _ _ dcp <- ds, let d = dcpCon dcp]

isResolvedDataConP :: ModName -> DataConP -> Bool
isResolvedDataConP m dp = F.symbol m == dcpModule dp

makeFDataDecls :: F.TCEmb Ghc.TyCon -> Ghc.TyCon -> DataPropDecl -> [(Ghc.DataCon, DataConP)]
               -> F.DataDecl
makeFDataDecls tce tc dd ctors = makeDataDecl tce tc (fst dd) ctors

makeDataDecl :: F.TCEmb Ghc.TyCon -> Ghc.TyCon -> DataDecl -> [(Ghc.DataCon, DataConP)]
             -> F.DataDecl
makeDataDecl tce tc dd ctors
  = F.DDecl
      { F.ddTyCon = ftc
      , F.ddVars  = length                $  GM.tyConTyVarsDef tc
      , F.ddCtors = makeDataCtor tce ftc <$> ctors
      }
  where
    ftc = F.symbolFTycon (tyConLocSymbol tc dd)

tyConLocSymbol :: Ghc.TyCon -> DataDecl -> LocSymbol
tyConLocSymbol tc dd = F.atLoc (tycName dd) (F.symbol tc)

-- [NOTE:ADT] We need to POST-PROCESS the 'Sort' so that:
-- 1. The poly tyvars are replaced with debruijn
--    versions e.g. 'List a_a1m' becomes 'List @(1)'
-- 2. The "self" type is replaced with just itself
--    (i.e. without any type applications.)

makeDataCtor :: F.TCEmb Ghc.TyCon -> F.FTycon -> (Ghc.DataCon, DataConP) -> F.DataCtor
makeDataCtor tce c (d, dp) = F.DCtor
  { F.dcName    = GM.namedLocSymbol d
  , F.dcFields  = makeDataFields tce c as xts
  }
  where
    as          = dcpFreeTyVars dp
    xts         = [ (fld x, t) | (x, t) <- reverse (dcpTyArgs dp) ]
    fld         = F.atLoc dp . fieldName d dp

fieldName :: Ghc.DataCon -> DataConP -> F.Symbol -> F.Symbol
fieldName d dp x
  | dcpIsGadt dp = F.suffixSymbol (F.symbol d) x
  | otherwise    = x

makeDataFields :: F.TCEmb Ghc.TyCon -> F.FTycon -> [RTyVar] -> [(F.LocSymbol, SpecType)]
               -> [F.DataField]
makeDataFields tce _c as xts = [ F.DField x (fSort t) | (x, t) <- xts]
  where
    su    = zip (F.symbol <$> as) [0..]
    fSort = F.substVars su . F.mapFVar (+ length as) . RT.rTypeSort tce

{- 
muSort :: F.FTycon -> Int -> F.Sort -> F.Sort
muSort c n  = V.mapSort tx
  where
    ct      = F.fTyconSort c
    me      = F.fTyconSelfSort c n
    tx t    = if t == me then ct else t
-}

--------------------------------------------------------------------------------
meetDataConSpec :: Bool -> F.TCEmb Ghc.TyCon -> [(Ghc.Var, SpecType)] -> [DataConP]
                -> [(Ghc.Var, SpecType)]
--------------------------------------------------------------------------------
meetDataConSpec allowTC emb xts dcs  = M.toList $ snd <$> L.foldl' upd dcm0 xts
  where
    dcm0                     = M.fromListWith meetM (dataConSpec' allowTC dcs)
    upd dcm (x, t)           = M.insert x (Ghc.getSrcSpan x, tx') dcm
                                where
                                  tx' = maybe t (meetX x t) (M.lookup x dcm)
    meetM (l,t) (_,t')       = (l, t `F.meet` t')
    meetX x t (sp', t')      = F.notracepp (_msg x t t') $ meetVarTypes emb (pprint x) (Ghc.getSrcSpan x, t) (sp', t')
    _msg x t t'              = "MEET-VAR-TYPES: " ++ showpp (x, t, t')

dataConSpec' :: Bool -> [DataConP] -> [(Ghc.Var, (Ghc.SrcSpan, SpecType))]
dataConSpec' allowTC = concatMap tx
  where
    tx dcp   =  [ (x, res) | (x, t0) <- dataConPSpecType allowTC dcp
                          , let t    = RT.expandProductType x t0
                          , let res  = (GM.fSrcSpan dcp, t)
                ]
--------------------------------------------------------------------------------
-- | Bare Predicate: DataCon Definitions ---------------------------------------
--------------------------------------------------------------------------------
makeConTypes :: ModName -> Bare.Env -> [(ModName, Ms.BareSpec)]
             -> Bare.Lookup ([(ModName, TyConP, Maybe DataPropDecl)], [[Located DataConP]])
makeConTypes myName env specs =
  Misc.concatUnzip <$> mapM (makeConTypes' myName env) specs


makeConTypes' :: ModName -> Bare.Env -> (ModName, Ms.BareSpec)
             -> Bare.Lookup ([(ModName, TyConP, Maybe DataPropDecl)], [[Located DataConP]])
makeConTypes' _myName env (name, spec) = do
  dcs'   <- canonizeDecls env name dcs
  let dcs'' = dataDeclSize spec dcs'
  let gvs = groupVariances dcs'' vdcs
  zong <- catLookups . map (uncurry (ofBDataDecl env name)) $ gvs
  return (unzip zong)
  where
    dcs  = Ms.dataDecls spec
    vdcs = Ms.dvariance spec


type DSizeMap = M.HashMap F.Symbol (F.Symbol, [F.Symbol])
normalizeDSize :: [([LocBareType], F.LocSymbol)] -> DSizeMap
normalizeDSize ds = M.fromList (concatMap go ds)
  where go (ts,x) = let xs = Mb.mapMaybe (getTc . val) ts
                    in [(tc, (val x, xs)) | tc <- xs]
        getTc (RAllT _ t _)  = getTc t
        getTc (RApp c _ _ _) = Just (val $ btc_tc c)
        getTc _ = Nothing

dataDeclSize :: Ms.BareSpec -> [DataDecl] -> [DataDecl]
dataDeclSize spec dcs = makeSize smap <$> dcs
  where smap = normalizeDSize $ Ms.dsize spec


makeSize :: DSizeMap -> DataDecl -> DataDecl
makeSize smap d
  | Just p <- M.lookup (F.symbol $ tycName d) smap
  = d {tycDCons = fmap (fmap (makeSizeCtor p)) (tycDCons d) }
  | otherwise
   = d

makeSizeCtor :: (F.Symbol, [F.Symbol]) -> DataCtor -> DataCtor
makeSizeCtor (s,xs) d = d {dcFields = Misc.mapSnd (mapBot go) <$> dcFields d}
  where
    go (RApp c ts rs r) | F.symbol c `elem` xs
                        = RApp c ts rs (r `F.meet` rsz)
    go t                = t
    rsz  = MkUReft (F.Reft (F.vv_, F.PAtom F.Lt
                                      (F.EApp (F.EVar s) (F.EVar F.vv_))
                                      (F.EApp (F.EVar s) (F.EVar selfSymbol))
                                      ))
                   mempty


catLookups :: [Bare.Lookup a] -> Bare.Lookup [a]
catLookups = sequence . Mb.mapMaybe skipResolve

skipResolve  :: Bare.Lookup a -> Maybe (Bare.Lookup a)
skipResolve (Left es) = left' (filter (not . isErrResolve) es)
skipResolve (Right v) = Just (Right v)

isErrResolve :: TError t -> Bool
isErrResolve ErrResolve {} = True
isErrResolve _             =  False

left' :: [e] -> Maybe (Either [e] a)
left' [] = Nothing
left' es = Just (Left es)


-- | 'canonizeDecls ds' returns a subset of 'ds' with duplicates, e.g. arising
--   due to automatic lifting (via 'makeHaskellDataDecls'). We require that the
--   lifted versions appear LATER in the input list, and always use those
--   instead of the unlifted versions.

canonizeDecls :: Bare.Env -> ModName -> [DataDecl] -> Bare.Lookup [DataDecl]
canonizeDecls env name dataDecls = do
  kds <- forM dataDecls $ \d -> do
           k <- dataDeclKey env name d
           return (fmap (, d) k)
  case Misc.uniqueByKey' selectDD (Mb.catMaybes kds) of
    Left  decls  -> Left [err decls]
    Right decls  -> return decls
            -- [ (k, d) | d <- ds, k <- rights [dataDeclKey env name d] ] 
  -- case Misc.uniqueByKey' selectDD kds of
    -- Left  decls  -> err    decls
    -- Right decls  -> decls
  where
    -- kds          = F.tracepp "canonizeDecls" [ (k, d) | d <- ds, k <- rights [dataDeclKey env name d] ] 
    err ds@(d:_) = {- uError $ -} errDupSpecs (pprint (tycName d)) (GM.fSrcSpan <$> ds)
    err _        = impossible Nothing "canonizeDecls"

dataDeclKey :: Bare.Env -> ModName -> DataDecl -> Bare.Lookup (Maybe F.Symbol)
dataDeclKey env name d = do
  tcMb  <- Bare.lookupGhcDnTyCon env name "canonizeDecls" (tycName d)
  case tcMb of
    Nothing ->
      return Nothing
    Just tc -> do
      _ <- checkDataCtors env name tc d (tycDCons d)
      return $ Just (F.symbol tc)

-- | Perform sanity check on the data constructors of a LH datatype declaration.
--
-- In the special situation where the LH datatype declaration is only used to
-- attach a termination measure, we pass 'Nothing', and our check always succeeds.
--
-- Otherwise, we check that the constructors match the constructors for the
-- Haskell datatype. This replaces an older check that only verified that any
-- constructor we list in a datatype is indeed a constructor of that corresponding
-- Haskell datatype.
--
-- We also check that constructors do not have duplicate fields.
--
checkDataCtors :: Bare.Env -> ModName -> Ghc.TyCon -> DataDecl -> Maybe [DataCtor] -> Bare.Lookup [DataCtor]
checkDataCtors _env _name _c _dd Nothing     = return []
checkDataCtors  env  name  c  dd (Just cons) = do
  -- The GHC data constructors (these are qualified)
  let dcs :: S.HashSet F.Symbol
      dcs = S.fromList . fmap F.symbol . Ghc.tyConDataCons $ c

  -- The data constructors in the spec (which we have to qualify for them to match the GHC data constructors)
  mbDcs <- mapM (Bare.failMaybe env name . Bare.lookupGhcDataCon env name "checkDataCtors" . dcName) cons
  let rdcs = S.fromList . fmap F.symbol . Mb.catMaybes $ mbDcs
  if dcs == rdcs
    then mapM checkDataCtorDupField cons
    else Left [errDataConMismatch (dataNameSymbol (tycName dd)) dcs rdcs]

-- | Checks whether the given data constructor has duplicate fields.
--
checkDataCtorDupField :: DataCtor -> Bare.Lookup DataCtor
checkDataCtorDupField d
  | x : _ <- dups = Left [err sym x]
  | otherwise     = return d
    where
      sym         = dcName   d
      xts         = dcFields d
      dups        = [ x | (x, ts) <- Misc.groupList xts, 2 <= length ts ]
      err lc x    = ErrDupField (GM.sourcePosSrcSpan $ loc lc) (pprint $ val lc) (pprint x)

selectDD :: (a, [DataDecl]) -> Either [DataDecl] DataDecl
selectDD (_,[d]) = Right d
selectDD (_, ds) = case [ d | d <- ds, tycKind d == DataReflected ] of
                     [d] -> Right d
                     _   -> Left  ds

groupVariances :: [DataDecl]
               -> [(LocSymbol, [Variance])]
               -> [(Maybe DataDecl, Maybe (LocSymbol, [Variance]))]
groupVariances dcs vdcs     =  merge (L.sort dcs) (L.sortBy (\x y -> compare (fst x) (fst y)) vdcs)
  where
    merge (d:ds) (v:vs)
      | F.symbol d == sym v = (Just d, Just v)  : merge ds vs
      | F.symbol d <  sym v = (Just d, Nothing) : merge ds (v:vs)
      | otherwise           = (Nothing, Just v) : merge (d:ds) vs
    merge []     vs         = (Nothing,) . Just <$> vs
    merge ds     []         = (,Nothing) . Just <$> ds
    sym                     = val . fst


-- | 'checkDataDecl' checks that the supplied DataDecl is indeed a refinement
--   of the GHC TyCon. We just check that the right tyvars are supplied
--   as errors in the names and types of the constructors will be caught
--   elsewhere. [e.g. tests/errors/BadDataDecl.hs]

checkDataDecl :: Ghc.TyCon -> DataDecl -> Bool
checkDataDecl c d = F.notracepp _msg (isGADT || cN == dN || null (tycDCons d))
  where
    _msg          = printf "checkDataDecl: D = %s, c = %s, cN = %d, dN = %d" (show d) (show c) cN dN
    cN            = length (GM.tyConTyVarsDef c)
    dN            = length (tycTyVars         d)
    isGADT        = Ghc.isGadtSyntaxTyCon c

getDnTyCon :: Bare.Env -> ModName -> DataName -> Bare.Lookup Ghc.TyCon
getDnTyCon env name dn = do
  tcMb <- Bare.lookupGhcDnTyCon env name "ofBDataDecl-1" dn
  case tcMb of
    Just tc -> return tc
    Nothing -> Left [ ErrBadData (GM.fSrcSpan dn) (pprint dn) "Unknown Type Constructor" ]
  --  ugh              = impossible Nothing "getDnTyCon"


-- FIXME: ES: why the maybes?
ofBDataDecl :: Bare.Env -> ModName -> Maybe DataDecl -> Maybe (LocSymbol, [Variance])
            -> Bare.Lookup ( (ModName, TyConP, Maybe DataPropDecl), [Located DataConP] )
ofBDataDecl env name (Just dd@(DataDecl tc as ps cts pos sfun pt _)) maybe_invariance_info = do
  let Loc lc lc' _ = dataNameSymbol tc
  let πs           = Bare.ofBPVar env name pos <$> ps
  let αs           = RTV . GM.symbolTyVar <$> as
  let n            = length αs
  let initmap      = zip (RT.uPVar <$> πs) [0..]
  tc'             <- getDnTyCon env name tc
  cts'            <- mapM (ofBDataCtor env name lc lc' tc' αs ps πs) (Mb.fromMaybe [] cts)
  unless (checkDataDecl tc' dd) (Left [err])
  let pd           = Bare.ofBareType env name lc (Just []) <$> F.tracepp "ofBDataDecl-prop" pt
  let tys          = [t | dcp <- cts', (_, t) <- dcpTyArgs dcp]
  let varInfo      = L.nub $  concatMap (getPsSig initmap True) tys
  let defPs        = varSignToVariance varInfo <$> [0 .. (length πs - 1)]
  let (tvi, pvi)   = case maybe_invariance_info of
                       Nothing     -> ([], defPs)
                       Just (_,is) -> let is_n = drop n is in
                                      (take n is, if null is_n then defPs else is_n)
  let tcp          = TyConP lc tc' αs πs tvi pvi sfun
  return ((name, tcp, Just (dd { tycDCons = cts }, pd)), Loc lc lc' <$> cts')
  where
    err            = ErrBadData (GM.fSrcSpan tc) (pprint tc) "Mismatch in number of type variables"

ofBDataDecl env name Nothing (Just (tc, is)) =
  case Bare.lookupGhcTyCon env name "ofBDataDecl-2" tc of
    Left e    -> Left e
    Right tc' -> Right ((name, TyConP srcpos tc' [] [] tcov tcontr Nothing, Nothing), [])
  where
    (tcov, tcontr) = (is, [])
    srcpos         = F.dummyPos "LH.DataType.Variance"

ofBDataDecl _ _ Nothing Nothing
  = panic Nothing "Bare.DataType.ofBDataDecl called on invalid inputs"

-- TODO:EFFECTS:ofBDataCon
ofBDataCtor :: Bare.Env
            -> ModName
            -> F.SourcePos
            -> F.SourcePos
            -> Ghc.TyCon
            -> [RTyVar]
            -> [PVar BSort]
            -> [PVar RSort]
            -> DataCtor
            -> Bare.Lookup DataConP
ofBDataCtor env name l l' tc αs ps πs dc = do
  c' <- Bare.lookupGhcDataCon env name "ofBDataCtor" (dcName dc)
  return (ofBDataCtorTc env name l l' tc αs ps πs dc c')

ofBDataCtorTc :: Bare.Env -> ModName -> F.SourcePos -> F.SourcePos ->
                 Ghc.TyCon -> [RTyVar] -> [PVar BSort] -> [PVar RSort] -> DataCtor -> Ghc.DataCon ->
                 DataConP
ofBDataCtorTc env name l l' tc αs ps πs _ctor@(DataCtor _c as _ xts res) c' =
  DataConP
    { dcpLoc        = l
    , dcpCon        = c'
    , dcpFreeTyVars = RT.symbolRTyVar <$> as
    , dcpFreePred   = πs
    , dcpTyConstrs  = cs
    , dcpTyArgs     = zts
    , dcpTyRes      = ot
    , dcpIsGadt     = isGadt
    , dcpModule     = F.symbol name
    , dcpLocE       = l'
    }
  where
    ts'           = Bare.ofBareType env name l (Just ps) <$> ts
    res'          = Bare.ofBareType env name l (Just ps) <$> res
    t0'           = dataConResultTy c' αs t0 res'
    _cfg          = getConfig env
    (yts, ot)     = qualifyDataCtor (not isGadt) name dLoc (zip xs ts', t0')
    zts           = zipWith (normalizeField c') [1..] (reverse yts)
    usedTvs       = S.fromList (ty_var_value <$> concatMap RT.freeTyVars (t0':ts'))
    cs            = [ p | p <- RT.ofType <$> Ghc.dataConTheta c', keepPredType usedTvs p ]
    (xs, ts)      = unzip xts
    t0            = case RT.famInstTyConType tc of
                      Nothing -> RT.gApp tc αs πs
                      Just ty -> RT.ofType ty
    isGadt        = Mb.isJust res
    dLoc          = F.Loc l l' ()

errDataConMismatch :: LocSymbol -> S.HashSet F.Symbol -> S.HashSet F.Symbol -> Error
errDataConMismatch d dcs rdcs = ErrDataConMismatch sp v (ppTicks <$> S.toList dcs) (ppTicks <$> S.toList rdcs)
  where
    v                 = pprint (val d)
    sp                = GM.sourcePosSrcSpan (loc d)

varSignToVariance :: Eq a => [(a, Bool)] -> a -> Variance
varSignToVariance varsigns i = case filter (\p -> fst p == i) varsigns of
                                []       -> Invariant
                                [(_, b)] -> if b then Covariant else Contravariant
                                _        -> Bivariant

getPsSig :: [(UsedPVar, a)] -> Bool -> SpecType -> [(a, Bool)]
getPsSig m pos (RAllT _ t r)
  = addps m pos r ++  getPsSig m pos t
getPsSig m pos (RApp _ ts rs r)
  = addps m pos r ++ concatMap (getPsSig m pos) ts
    ++ concatMap (getPsSigPs m pos) rs
getPsSig m pos (RVar _ r)
  = addps m pos r
getPsSig m pos (RAppTy t1 t2 r)
  = addps m pos r ++ getPsSig m pos t1 ++ getPsSig m pos t2
getPsSig m pos (RFun _ _ t1 t2 r)
  = addps m pos r ++ getPsSig m pos t2 ++ getPsSig m (not pos) t1
getPsSig m pos (RHole r)
  = addps m pos r
getPsSig _ _ z
  = panic Nothing $ "getPsSig" ++ show z

getPsSigPs :: [(UsedPVar, a)] -> Bool -> SpecProp -> [(a, Bool)]
getPsSigPs m pos (RProp _ (RHole r)) = addps m pos r
getPsSigPs m pos (RProp _ t) = getPsSig m pos t

addps :: [(UsedPVar, a)] -> b -> UReft t -> [(a, b)]
addps m pos (MkUReft _ ps) = (, pos) . f  <$> pvars ps
  where
    f = Mb.fromMaybe (panic Nothing "Bare.addPs: notfound") . (`L.lookup` m) . RT.uPVar

keepPredType :: S.HashSet RTyVar -> SpecType -> Bool
keepPredType tvs p
  | Just (tv, _) <- eqSubst p = S.member tv tvs
  | otherwise                 = True


-- | This computes the result of a `DataCon` application.
--   For 'isVanillaDataCon' we can just use the `TyCon`
--   applied to the relevant tyvars.
dataConResultTy :: Ghc.DataCon
                -> [RTyVar]         -- ^ DataConP ty-vars
                -> SpecType         -- ^ vanilla result type
                -> Maybe SpecType   -- ^ user-provided result type
                -> SpecType
dataConResultTy c _ _ (Just t) = F.notracepp ("dataConResultTy-3 : vanilla = " ++ show (Ghc.isVanillaDataCon c) ++ " : ") t
dataConResultTy c _ t _
  | Ghc.isVanillaDataCon c     = F.notracepp ("dataConResultTy-1 : " ++ F.showpp c) t
  | otherwise                  = F.notracepp ("dataConResultTy-2 : " ++ F.showpp c) $ RT.ofType ct
  where
    (_,_,_,_,_,ct)             = Ghc.dataConFullSig c

eqSubst :: SpecType -> Maybe (RTyVar, SpecType)
eqSubst (RApp c [_, _, RVar a _, t] _ _)
  | rtc_tc c == Ghc.eqPrimTyCon = Just (a, t)
eqSubst _                       = Nothing

normalizeField :: Ghc.DataCon -> Int -> (F.Symbol, a) -> (F.Symbol, a)
normalizeField c i (x, t)
  | isTmp x   = (xi, t)
  | otherwise = (x , t)
  where
    isTmp     = F.isPrefixOfSym F.tempPrefix
    xi        = makeDataConSelector Nothing c i

-- | `qualifyDataCtor` qualfies the field names for each `DataCtor` to
--   ensure things work properly when exported.
type CtorType = ([(F.Symbol, SpecType)], SpecType)

qualifyDataCtor :: Bool -> ModName -> F.Located a -> CtorType -> CtorType
qualifyDataCtor qualFlag name l ct@(xts, st)
 | qualFlag  = (xts', t')
 | otherwise = ct
 where
   t'        = F.subst su <$> st
   xts'      = [ (qx, F.subst su t)       | (qx, t, _) <- fields ]
   su        = F.mkSubst [ (x, F.eVar qx) | (qx, _, Just x) <- fields ]
   fields    = [ (qx, t, mbX) | (x, t) <- xts, let (mbX, qx) = qualifyField name (F.atLoc l x) ]

qualifyField :: ModName -> LocSymbol -> (Maybe F.Symbol, F.Symbol)
qualifyField name lx
 | needsQual = (Just x, F.notracepp msg $ qualifyModName name x)
 | otherwise = (Nothing, x)
 where
   msg       = "QUALIFY-NAME: " ++ show x ++ " in module " ++ show (F.symbol name)
   x         = val lx
   needsQual = not (isWiredIn lx)

checkRecordSelectorSigs :: [(Ghc.Var, LocSpecType)] -> [(Ghc.Var, LocSpecType)]
checkRecordSelectorSigs vts = [ (v, take1 v lspecTys) | (v, lspecTys) <- Misc.groupList vts ]
  where
    take1 v lsts            = case Misc.nubHashOn (showpp . val) lsts of
                                [t]    -> t
                                (t:ts) -> Ex.throw (ErrDupSpecs (GM.fSrcSpan t) (pprint v) (GM.fSrcSpan <$> ts) :: Error)
                                _      -> impossible Nothing "checkRecordSelectorSigs"


strengthenClassSel :: Ghc.Var -> LocSpecType -> LocSpecType
strengthenClassSel v lt = lt { val = st }
 where
  st = runReader (go (F.val lt)) (1, [])
  s = GM.namedLocSymbol v
  extend :: F.Symbol -> (Int, [F.Symbol]) -> (Int, [F.Symbol])
  extend x (i, xs) = (i + 1, x : xs)
  go :: SpecType -> Reader (Int, [F.Symbol]) SpecType
  go (RAllT a t r) = RAllT a <$> go t <*> pure r
  go (RAllP p t  ) = RAllP p <$> go t
  go (RFun x i tx t r) | isEmbeddedClass tx =
    RFun x i tx <$> go t <*> pure r
  go (RFun x i tx t r) = do
    x' <- unDummy x <$> reader fst
    r' <- singletonApp s <$> (L.reverse <$> reader snd)
    RFun x' i tx <$> local (extend x') (go t) <*> pure (F.meet r r')
  go t = RT.strengthen t . singletonApp s . L.reverse <$> reader snd

singletonApp :: F.Symbolic a => F.LocSymbol -> [a] -> UReft F.Reft
singletonApp s ys = MkUReft r mempty
  where r = F.exprReft (F.mkEApp s (F.eVar <$> ys))


unDummy :: F.Symbol -> Int -> F.Symbol
unDummy x i | x /= F.dummySymbol = x
            | otherwise          = F.symbol ("_cls_lq" ++ show i)

makeRecordSelectorSigs :: Bare.Env -> ModName -> [Located DataConP] -> [(Ghc.Var, LocSpecType)]
makeRecordSelectorSigs env name = checkRecordSelectorSigs . concatMap makeOne
  where
  makeOne (Loc l l' dcp)
    | Just cls <- maybe_cls
    = let cfs = Ghc.classAllSelIds cls in
        fmap ((,) <$> fst <*> uncurry strengthenClassSel)
          [(v, Loc l l' t)| (v,t) <- zip cfs (reverse $ fmap snd args)]
    | null fls                    --    no field labels
    || any (isFunTy . snd) args && not (higherOrderFlag env)   -- OR function-valued fields
    || dcpIsGadt dcp              -- OR GADT style datcon
    = []
    | otherwise
    = [ (v, t) | (Just v, t) <- zip fs ts ]
    where
      maybe_cls = Ghc.tyConClass_maybe (Ghc.dataConTyCon dc)
      dc  = dcpCon dcp
      fls = Ghc.dataConFieldLabels dc
      fs  = Bare.lookupGhcNamedVar env name . Ghc.flSelector <$> fls
      ts :: [ LocSpecType ]
      ts = [ Loc l l' (mkArrow (zip (makeRTVar <$> dcpFreeTyVars dcp) (repeat mempty)) []
                                 [] [(z, classRFInfo True, res, mempty)]
                                 (dropPreds (F.subst su t `RT.strengthen` mt)))
             | (x, t) <- reverse args -- NOTE: the reverse here is correct
             , let vv = rTypeValueVar t
               -- the measure singleton refinement, eg `v = getBar foo`
             , let mt = RT.uReft (vv, F.PAtom F.Eq (F.EVar vv) (F.EApp (F.EVar x) (F.EVar z)))
             ]

      su   = F.mkSubst [ (x, F.EApp (F.EVar x) (F.EVar z)) | x <- fst <$> args ]
      args = dcpTyArgs dcp
      z    = "lq$recSel"
      res  = dropPreds (dcpTyRes dcp)

      -- FIXME: this is clearly imprecise, but the preds in the DataConP seem
      -- to be malformed. If we leave them in, tests/pos/kmp.hs fails with
      -- a malformed predicate application. Niki, help!!
      dropPreds = fmap (\(MkUReft r _ps) -> MkUReft r mempty)
