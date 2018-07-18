{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Language.Haskell.Liquid.Bare.DataType
  ( 
    DataConMap
  , dataConMap

  -- * Names for accessing Data Constuctors 
  , makeDataConChecker
  , makeDataConSelector 
  , addClassEmbeds

  -- * Constructors
  , makeDataDecls
  , makeConTypes
  , makeRecordSelectorSigs
  -- , makeTyConEmbeds
  -- , meetDataConSpec

  ) where

-- import           TysPrim
-- import           Name                                   (getSrcSpan)
-- import           SrcLoc                                 (SrcSpan)

import           Prelude                                hiding (error)
import qualified InstEnv as Ghc 
import qualified TyCon   as Ghc 
import qualified DataCon as Ghc 
import qualified Type    as Ghc 
import qualified TyCoRep as Ghc 
import qualified Class   as Ghc
import qualified TysWiredIn as Ghc 
-- import           Text.Parsec
-- import           Var
-- import           Data.Maybe
-- import           Language.Haskell.Liquid.GHC.TypeRep

import           Control.Monad                          (forM_, when) -- , (>=>))
import           Control.Monad.State                    (gets)
import qualified Control.Exception                      as Ex
import qualified Data.List                              as L
import qualified Data.HashMap.Strict                    as M
import qualified Data.HashSet                           as S
import qualified Data.Maybe                             as Mb 

import qualified Language.Fixpoint.Types.Visitor        as V
import qualified Language.Fixpoint.Types                as F
import qualified Language.Haskell.Liquid.GHC.Misc       as GM 
import           Language.Haskell.Liquid.Types.PredType (dataConWorkRep, dataConPSpecType)
import qualified Language.Haskell.Liquid.Types.RefType  as RT
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.Meet
import qualified Language.Fixpoint.Misc                 as Misc
import qualified Language.Haskell.Liquid.Misc           as Misc
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.WiredIn

import qualified Language.Haskell.Liquid.Measure        as Ms
import           Language.Haskell.Liquid.Bare.Types 
import           Language.Haskell.Liquid.Bare.Resolve 

-- import qualified Language.Haskell.Liquid.Bare.Misc      as GM
-- import           Language.Haskell.Liquid.Bare.Env
-- import           Language.Haskell.Liquid.Bare.Lookup
-- import           Language.Haskell.Liquid.Bare.OfType
import           Text.Printf                     (printf)
import           Text.PrettyPrint.HughesPJ       ((<+>))
-- import           Debug.Trace (trace)

--------------------------------------------------------------------------------
-- | 'DataConMap' stores the names of those ctor-fields that have been declared
--   as SMT ADTs so we don't make up new names for them.
--------------------------------------------------------------------------------

dataConMap :: [F.DataDecl] -> DataConMap
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
makeDataConChecker d
  = F.testSymbol (F.symbol d)

--------------------------------------------------------------------------------
-- | 'makeDataConSelector d' creates the selector `select$d$i`
--   which projects the i-th field of a constructed value.
--   e.g. `select$Cons$1` and `select$Cons$2` are respectively
--   equivalent to `head` and `tail`.
--------------------------------------------------------------------------------
makeDataConSelector :: Maybe DataConMap -> Ghc.DataCon -> Int -> F.Symbol
makeDataConSelector dmMb d i = M.lookupDefault def (F.symbol d, i) dm
  where 
    dm                       = Mb.fromMaybe M.empty dmMb 
    def                      = makeDataConSelector' d i

 {- 
  case mbDm of
  Nothing -> def
  Just dm -> M.lookupDefault def (F.symbol d, i) dm
  where
 -} 

makeDataConSelector' :: Ghc.DataCon -> Int -> F.Symbol
makeDataConSelector' d i
  = symbolMeasure "$select" (dcSymbol d) (Just i)

dcSymbol :: Ghc.DataCon -> F.Symbol
dcSymbol = {- simpleSymbolVar -} F.symbol . Ghc.dataConWorkId

symbolMeasure :: String -> F.Symbol -> Maybe Int -> F.Symbol
symbolMeasure f d iMb = foldr1 F.suffixSymbol (dcPrefix : F.symbol f : d : rest)
  where
    rest          = maybe [] (Misc.singleton . F.symbol . show) iMb


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
makeFamInstEmbeds cs0 embs = L.foldl' embed embs famInstSorts
  where
    famInstSorts          = F.notracepp "famInstTcs"
                            [ (c, RT.typeSort embs ty)
                                | c   <- cs
                                , ty  <- Mb.maybeToList (famInstTyConType c) ]
    embed embs (c, t)     = F.tceInsert c t F.NoArgs embs
    cs                    = F.notracepp "famInstTcs-all" cs0

famInstTyConType :: Ghc.TyCon -> Maybe Ghc.Type
famInstTyConType c = case Ghc.tyConFamInst_maybe c of
  Just (c', ts) -> Just (famInstType (Ghc.tyConArity c) c' ts)
  Nothing       -> Nothing

famInstType :: Int -> Ghc.TyCon -> [Ghc.Type] -> Ghc.Type
famInstType n c ts = Ghc.mkTyConApp c (take (length ts - n) ts)

{- | [NOTE:FamInstEmbeds] For various reasons, GHC represents family instances
     in two ways: (1) As an applied type, (2) As a special tycon.
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
              -> [(Ghc.DataCon, Located DataConP)]
              -> [F.DataDecl]
makeDataDecls cfg tce name tds ds
  | makeDecls = [ makeFDataDecls tce tc dd ctors
                | (tc, (dd, ctors)) <- groupDataCons tds' ds
                , tc /= Ghc.listTyCon
                ]
  | otherwise = []
  where
    makeDecls = exactDCFlag cfg && not (noADT cfg)
    tds'      = resolveTyCons name tds

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
resolveTyCons m mtds = [(tc, (m, d)) | (tc, mds) <- M.toList tcDecls
                                     , (m, d)    <- Mb.maybeToList $ resolveDecls m tc mds ]
  where
    tcDecls          = Misc.group [ (tc, (m, d)) | (m, tc, d) <- mtds ]

-- | See [NOTE:Orphan-TyCons], the below function tells us which of (possibly many)
--   DataDecls to use.
resolveDecls :: ModName -> Ghc.TyCon -> Misc.ListNE (ModName, DataPropDecl)
             -> Maybe (ModName, DataPropDecl)
resolveDecls mName tc mds  = Misc.firstMaybes $ (`L.find` mds) <$> [ isHomeDef , isMyDef]
  where
    isMyDef                = (mName ==)             . fst
    isHomeDef              = (tcHome ==) . F.symbol . fst
    tcHome                 = GM.takeModuleNames (F.symbol tc)


groupDataCons :: [(Ghc.TyCon, (ModName, DataPropDecl))]
              -> [(Ghc.DataCon, Located DataConP)]
              -> [(Ghc.TyCon, (DataPropDecl, [(Ghc.DataCon, DataConP)]))]
groupDataCons tds ds = [ (tc, (d, dds')) | (tc, ((m, d), dds)) <- tcDataCons
                                         , let dds' = filter (isResolvedDataConP m . snd) dds
                       ]
  where
    tcDataCons       = M.toList $ M.intersectionWith (,) declM ctorM
    declM            = M.fromList tds
    ctorM            = Misc.group [(Ghc.dataConTyCon d, (d, val dp)) | (d, dp) <- ds]

isResolvedDataConP :: ModName -> DataConP -> Bool
isResolvedDataConP m dp = F.symbol m == dcpModule dp

makeFDataDecls :: F.TCEmb Ghc.TyCon -> Ghc.TyCon -> DataPropDecl -> [(Ghc.DataCon, DataConP)]
               -> F.DataDecl
makeFDataDecls tce tc dd ctors = makeDataDecl tce tc (fst dd) ctors
                               -- ++ maybeToList (makePropDecl tce tc dd) -- TODO: AUTO-INDPRED

makeDataDecl :: F.TCEmb Ghc.TyCon -> Ghc.TyCon -> DataDecl -> [(Ghc.DataCon, DataConP)]
             -> F.DataDecl
makeDataDecl tce tc dd ctors
  = F.DDecl
      { F.ddTyCon = ftc
      , F.ddVars  = length                $  tycTyVars dd
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
    as          = freeTyVars dp
    xts         = [ (fld x, t) | (x, t) <- reverse (tyArgs dp) ]
    fld         = Loc (dc_loc dp) (dc_locE dp) . fieldName d dp

fieldName :: Ghc.DataCon -> DataConP -> F.Symbol -> F.Symbol
fieldName d dp x
  | dcpIsGadt dp = F.suffixSymbol (F.symbol d) x
  | otherwise    = x

makeDataFields :: F.TCEmb Ghc.TyCon -> F.FTycon -> [RTyVar] -> [(F.LocSymbol, SpecType)]
               -> [F.DataField]
makeDataFields tce c as xts = [ F.DField x (fSort t) | (x, t) <- xts]
  where
    su                      = zip ({- rtyVarUniqueSymbol -} F.symbol <$> as) [0..]
    fSort                   = muSort c (length as) . F.substVars su . RT.rTypeSort tce

muSort :: F.FTycon -> Int -> F.Sort -> F.Sort
muSort c n  = V.mapSort tx
  where
    ct      = F.fTyconSort c
    me      = F.fTyconSelfSort c n
    tx t    = if t == me then ct else t




--------------------------------------------------------------------------------
{- | NOTE:AUTO-INDPRED (tests/todo/IndPred1.hs)
-- DO NOT DELETE
-- RJ: too hard, too brittle, I _thought_ we could just
-- generate the F.DataDecl, but really, you need the GHC
-- names for the Prop-Ctor if you want to be able to `import`
-- a predicate across modules. Seems a LOT easier to just have
-- the program explicitly create the the proposition type
-- e.g. as shownn in (tests/pos/IndPred0.hs)
--------------------------------------------------------------------------------

type SpecTypeRep  = RTypeRep RTyCon RTyVar RReft

-- | 'makePropDecl' creates the 'F.DataDecl' for the *proposition* described
--   by the corresponding 'TyCon' / 'DataDecl', e.g. tests/pos/IndPred0.hs
makePropDecl :: F.TCEmb TyCon -> TyCon -> DataPropDecl -> Maybe F.DataDecl
makePropDecl tce tc (dd, pd) = makePropTyDecl tce tc dd <$> pd

makePropTyDecl :: F.TCEmb TyCon -> TyCon -> DataDecl -> SpecType -> F.DataDecl
makePropTyDecl tce tc dd t
  = F.DDecl
    { F.ddTyCon = ftc
    , F.ddVars  = length (ty_vars tRep)
    , F.ddCtors = [ makePropTyCtor tce ftc tRep ]
    }
  where
    ftc         = propFTycon tc dd
    tRep        = toRTypeRep t

propFTycon :: TyCon -> DataDecl -> F.FTycon
propFTycon tc = F.symbolFTycon . fmap (`F.suffixSymbol` F.propConName) . tyConLocSymbol tc

makePropTyCtor :: F.TCEmb TyCon -> F.FTycon -> SpecTypeRep -> F.DataCtor
makePropTyCtor tce ftc t
  = F.DCtor
    { F.dcName   = F.fTyconSymbol ftc
    , F.dcFields = makePropTyFields tce ftc t
    }

makePropTyFields :: F.TCEmb TyCon -> F.FTycon -> SpecTypeRep -> [F.DataField]
makePropTyFields tce ftc t = makeDataFields tce ftc as xts
  where
    as                     = [ a | RTVar a _ <- ty_vars t ]
    xts                    = zipWith (\i t -> (fld i, t)) [0..] (ty_args t)
    tcSym                  = F.fTyconSymbol ftc
    fld                    = F.atLoc tcSym
                           . GM.symbolMeasure "propField" (val tcSym)
                           . Just

isPropDecl :: F.DataDecl -> Bool
isPropDecl d =  (F.isSuffixOfSym F.propConName . F.symbol . F.ddTyCon $ d)
              && (length (F.ddCtors d) == 1)

qualifyDataDecl :: ModName -> DataDecl -> DataDecl
qualifyDataDecl name d = d { tycName = qualifyName name (tycName d)}

qualifyName :: ModName -> LocSymbol -> LocSymbol
qualifyName n x = F.atLoc x $ GM.qualifySymbol nSym (val x)
  where
    nSym        = GM.takeModuleNames (F.symbol n)

-}

--------------------------------------------------------------------------------
-- | Bare Predicate: DataCon Definitions ---------------------------------------
--------------------------------------------------------------------------------
makeConTypes :: (ModName, Ms.BareSpec) 
             -> ( [(ModName, Ghc.TyCon, TyConP, Maybe DataPropDecl)]
                , [[(Ghc.DataCon, Located DataConP)]]              )
makeConTypes (name, spec) = undefined 
-- inModule name $
--   makeConTypes' name (Ms.dataDecls spec) (Ms.dvariance spec)

{- BAREOLD
makeConTypes' :: ModName -> [DataDecl] -> [(LocSymbol, [Variance])]
              -> BareM ( [(ModName, TyCon, TyConP, Maybe DataPropDecl)]
                       , [[(DataCon, Located DataConP)]])
makeConTypes' name dcs vdcs = do
  dcs' <- F.notracepp "CANONIZED-DECLS" <$> canonizeDecls dcs
  unzip <$> mapM (uncurry (ofBDataDecl name)) (groupVariances dcs' vdcs)

-- | 'canonizeDecls ds' returns a subset of 'ds' with duplicates, e.g. arising
--   due to automatic lifting (via 'makeHaskellDataDecls'). We require that the
--   lifted versions appear LATER in the input list, and always use those
--   instead of the unlifted versions.

canonizeDecls :: [DataDecl] -> BareM [DataDecl]
canonizeDecls ds = do
  ks <- mapM key ds
  case Misc.uniqueByKey' selectDD (zip ks ds) of
    Left  ds     -> err    ds
    Right ds     -> return ds
  where
    key          = fmap F.symbol . lookupGhcDnTyCon "canonizeDecls" . tycName
    err ds@(d:_) = uError (errDupSpecs (pprint $ tycName d)(GM.fSrcSpan <$> ds))
    err _        = impossible Nothing "canonizeDecls"

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
    merge []     vs         = ((Nothing,) . Just) <$> vs
    merge ds     []         = ((,Nothing) . Just) <$> ds
    sym                     = val . fst

dataConSpec' :: [(DataCon, DataConP)] -> [(Var, (SrcSpan, SpecType))]
dataConSpec' dcs = concatMap tx dcs
  where
    sspan z      = GM.sourcePos2SrcSpan (dc_loc z) (dc_locE z)
    tx (dc, dcp) = [ (x, (sspan dcp, t)) | (x, t0) <- dataConPSpecType dc dcp
                                         , let t  = F.notracepp ("expandProductType" ++ showpp (x, t0)) $ RT.expandProductType x t0  ]

    -- tx (dc, dcp) = [ (x, (sspan dcp, t)) | (x, t) <- RT.mkDataConIdsTy dc (dataConPSpecType dc dcp) ] -- HEREHEREHEREHERE-1089


meetDataConSpec :: F.TCEmb TyCon -> [(Var, SpecType)] -> [(DataCon, DataConP)] -> [(Var, SpecType)]
meetDataConSpec emb xts dcs  = M.toList $ snd <$> L.foldl' upd dcm0 (F.notracepp "meetDataConSpec" xts)
  where
    dcm0                     = M.fromList $ dataConSpec' dcs
    upd dcm (x, t)           = M.insert x (getSrcSpan x, tx') dcm
                                where
                                  tx' = maybe t (meetX x t) (M.lookup x dcm)
    meetX x t (sp', t')      = meetVarTypes emb (pprint x) (getSrcSpan x, t) (sp', t')

checkDataCtors :: TyCon -> [DataCtor] -> BareM ()
checkDataCtors c ds = do
  mapM_ checkDataCtor ds
  let dcs = S.fromList . fmap F.symbol $ tyConDataCons c
  forM_ ds $ \d -> do
    let dn = dcName d
    x     <- F.symbol <$> lookupGhcDataCon dn
    when (not (S.member x dcs)) (uError (errInvalidDataCon c dn))

errInvalidDataCon :: TyCon -> LocSymbol -> UserError
errInvalidDataCon c d = ErrBadData sp (pprint (val d)) msg
  where
    sp                = GM.sourcePosSrcSpan (loc d)
    msg               = ppVar c <+> "is not the type constructor"

checkDataCtor :: DataCtor -> BareM ()
checkDataCtor (DataCtor lc _ xts _)
  | x : _ <- dups = Ex.throw (err lc x :: UserError)
  | otherwise     = return ()
    where
      dups        = [ x | (x, ts) <- Misc.groupList xts, 2 <= length ts ]
      err lc x    = ErrDupField (GM.sourcePosSrcSpan $ loc lc) (pprint $ val lc) (pprint x)

-- | 'checkDataDecl' checks that the supplied DataDecl is indeed a refinement
--   of the GHC TyCon. We just check that the right tyvars are supplied
--   as errors in the names and types of the constructors will be caught
--   elsewhere. [e.g. tests/errors/BadDataDecl.hs]

checkDataDecl :: TyCon -> DataDecl -> Bool
checkDataDecl c d = F.notracepp _msg (cN == dN || null (tycDCons d))
  where
    _msg          = printf "checkDataDecl: c = %s, cN = %d, dN = %d" (show c) cN dN
    cN            = length (GM.tyConTyVarsDef c)
    dN            = length (tycTyVars         d)

-- FIXME: ES: why the maybes?
ofBDataDecl :: ModName
            -> Maybe DataDecl
            -> (Maybe (LocSymbol, [Variance]))
            -> BareM ((ModName, TyCon, TyConP, Maybe DataPropDecl), [(DataCon, Located DataConP)])
ofBDataDecl name (Just dd@(D tc as ps ls cts _ sfun pt _)) maybe_invariance_info
  = do πs            <- mapM ofBPVar ps
       tc'           <- lookupGhcDnTyCon "ofBDataDecl" tc
       when (not $ checkDataDecl tc' dd) (Ex.throw err)
       checkDataCtors tc' cts
       cts'          <- mapM (ofBDataCtor name lc lc' tc' αs ps ls πs) cts
       pd            <- mapM (mkSpecType' lc []) pt
       let tys        = [t | (_, dcp) <- cts', (_, t) <- tyArgs dcp]
       let initmap    = zip (RT.uPVar <$> πs) [0..]
       let varInfo    = L.nub $  concatMap (getPsSig initmap True) tys
       let defPs      = varSignToVariance varInfo <$> [0 .. (length πs - 1)]
       let (tvi, pvi) = f defPs
       let tcp        = TyConP lc αs πs ls tvi pvi sfun
       return ((name, tc', tcp, Just (dd { tycDCons = cts }, pd)), (Misc.mapSnd (Loc lc lc') <$> cts'))
    where
       err          = ErrBadData (GM.fSrcSpan tc) (pprint tc) "Mismatch in number of type variables" :: UserError
       αs           = RTV . GM.symbolTyVar <$> as
       n            = length αs
       Loc lc lc' _ = dataNameSymbol tc
       f defPs      = case maybe_invariance_info of
                       { Nothing -> ([], defPs);
                         Just (_,is) -> (take n is, if null (drop n is) then defPs else (drop n is))}

ofBDataDecl name Nothing (Just (tc, is))
  = do tc'        <- lookupGhcTyCon "ofBDataDecl" tc
       return ((name, tc', TyConP srcpos [] [] [] tcov tcontr Nothing, Nothing), [])
  where
    (tcov, tcontr) = (is, [])
    srcpos = F.dummyPos "LH.DataType.Variance"

ofBDataDecl _ Nothing Nothing
  = panic Nothing "Bare.DataType.ofBDataDecl called on invalid inputs"

varSignToVariance :: Eq a => [(a, Bool)] -> a -> Variance
varSignToVariance varsigns i = case filter (\p -> fst p == i) varsigns of
                                []       -> Invariant
                                [(_, b)] -> if b then Covariant else Contravariant
                                _        -> Bivariant

getPsSig :: [(UsedPVar, a)] -> Bool -> SpecType -> [(a, Bool)]
getPsSig m pos (RAllT _ t)
  = getPsSig m pos t
getPsSig m pos (RApp _ ts rs r)
  = addps m pos r ++ concatMap (getPsSig m pos) ts
    ++ concatMap (getPsSigPs m pos) rs
getPsSig m pos (RVar _ r)
  = addps m pos r
getPsSig m pos (RAppTy t1 t2 r)
  = addps m pos r ++ getPsSig m pos t1 ++ getPsSig m pos t2
getPsSig m pos (RFun _ t1 t2 r)
  = addps m pos r ++ getPsSig m pos t2 ++ getPsSig m (not pos) t1
getPsSig m pos (RHole r)
  = addps m pos r
getPsSig _ _ z
  = panic Nothing $ "getPsSig" ++ show z

getPsSigPs :: [(UsedPVar, a)] -> Bool -> SpecProp -> [(a, Bool)]
getPsSigPs m pos (RProp _ (RHole r)) = addps m pos r
getPsSigPs m pos (RProp _ t) = getPsSig m pos t

addps :: [(UsedPVar, a)] -> b -> UReft t -> [(a, b)]
addps m pos (MkUReft _ ps _) = (flip (,)) pos . f  <$> pvars ps
  where f = fromMaybe (panic Nothing "Bare.addPs: notfound") . (`L.lookup` m) . RT.uPVar

-- TODO:EFFECTS:ofBDataCon
ofBDataCtor :: ModName
            -> SourcePos
            -> SourcePos
            -> TyCon
            -> [RTyVar]
            -> [PVar BSort]
            -> [F.Symbol]
            -> [PVar RSort]
            -> DataCtor
            -> BareM (DataCon, DataConP)
ofBDataCtor name l l' tc αs ps ls πs (DataCtor c _ xts res) = do
  c'           <- lookupGhcDataCon c
  ts'          <- mapM (mkSpecType' l ps) ts
  res'         <- mapM (mkSpecType' l ps) res
  let t0'       = F.notracepp ("dataConResultTy c' = " ++ show c' ++ " res' = " ++ show res') $ dataConResultTy c' αs t0 res'
  cfg          <- gets beConfig
  let (yts, ot) = F.notracepp ("OFBDataCTOR: " ++ show c' ++ " " ++ show (isVanillaDataCon c', res') ++ " " ++ show isGadt)
                $ qualifyDataCtor (exactDCFlag cfg && not isGadt) name dLoc (zip xs ts', t0')
  let zts       = zipWith (normalizeField c') [1..] (reverse yts)

  let usedTvs   = S.fromList (ty_var_value <$> concatMap RT.freeTyVars (t0':ts'))
  -- let cs        = RT.ofType <$> dataConStupidTheta c'
  let cs        = [ p | p <- RT.ofType <$> dataConTheta c', keepPredType usedTvs p ]
  return          (c', DataConP l αs πs ls cs zts ot isGadt (F.symbol name) l')
  where
    (xs, ts)    = unzip xts
    t0          = case famInstTyConType tc of
                    Nothing -> RT.gApp tc αs πs
                    Just ty -> RT.ofType ty
    -- nFlds    = length xts
    -- rs       = [RT.rVar α | RTV α <- αs]
    -- t0       = F.tracepp "t0 = " $ RT.rApp tc rs (rPropP [] . pdVarReft <$> πs) mempty -- 1089 HEREHERE use the SPECIALIZED type?
    isGadt      = isJust res
    dLoc        = F.Loc l l' ()


keepPredType :: S.HashSet RTyVar -> SpecType -> Bool
keepPredType tvs p
  | Just (tv, _) <- eqSubst p = S.member tv tvs
  | otherwise                 = True


-- | This computes the result of a `DataCon` application.
--   For 'isVanillaDataCon' we can just use the `TyCon`
--   applied to the relevant tyvars.
dataConResultTy :: DataCon
                -> [RTyVar]         -- ^ DataConP ty-vars
                -> SpecType         -- ^ vanilla result type
                -> Maybe SpecType   -- ^ user-provided result type
                -> SpecType
dataConResultTy _ _ _ (Just t) = t
dataConResultTy c αs t _
  | isVanillaDataCon c         = t
  | False                      = F.notracepp "RESULT-TYPE:" $ RT.subsTyVars_meet (gadtSubst αs c) t
dataConResultTy c _ _ _        = RT.ofType t
  where
    (_,_,_,_,_,t)              = {- GM.tracePpr ("FULL-SIG:" ++ show c ++ " -- repr : " ++ GM.showPpr (_tr0, _tr1, _tr2)) $ -} dataConFullSig c
    _tr0                        = dataConRepType c
    _tr1                        = varType $ dataConWorkId c
    _tr2                        = varType $ dataConWrapId c

-- RTVar RTyVar RSort

gadtSubst :: [RTyVar] -> DataCon -> [(RTyVar, RSort, SpecType)]
gadtSubst as c  = mkSubst (Misc.join aBs bTs)
  where
    bTs         = [ (b, t) |  Just (b, t) <- eqSubst <$> ty_args workR ]
    aBs         = zip as bs
    bs          = ty_var_value <$> ty_vars workR
    workR       = dataConWorkRep c
    mkSubst bTs = [ (b, toRSort t, t) | (b, t) <- bTs ]

eqSubst :: SpecType -> Maybe (RTyVar, SpecType)
eqSubst (RApp c [_, _, (RVar a _), t] _ _)
  | rtc_tc c == eqPrimTyCon = Just (a, t)
eqSubst _                   = Nothing

normalizeField :: DataCon -> Int -> (F.Symbol, a) -> (F.Symbol, a)
normalizeField c i (x, t)
  | isTmp x   = (xi, t)
  | otherwise = (x , t)
  where
    isTmp     = F.isPrefixOfSym F.tempPrefix
    xi        = GM.makeDataConSelector Nothing c i

-- | `qualifyDataCtor` qualfies the field names for each `DataCtor` to
--   ensure things work properly when exported.
type CtorType = ([(F.Symbol, SpecType)], SpecType)

qualifyDataCtor :: Bool -> ModName -> F.Located a -> CtorType -> CtorType
qualifyDataCtor qualFlag name l ct@(xts, t)
 | qualFlag  = (xts', t')
 | otherwise = ct
 where
   t'        = F.subst su <$> t
   xts'      = [ (qx, F.subst su t)       | (qx, t, _) <- fields ]
   su        = F.notracepp "F-ING subst" $ F.mkSubst [ (x, F.eVar qx) | (qx, _, Just x) <- fields ]
   fields    = [ (qx, t, mbX) | (x, t) <- xts, let (mbX, qx) = qualifyField name (F.atLoc l x) ]

qualifyField :: ModName -> LocSymbol -> (Maybe F.Symbol, F.Symbol)
qualifyField name lx
 | needsQual = (Just x, F.notracepp msg $ qualifyModName name x)
 | otherwise = (Nothing, x)
 where
   msg       = "QUALIFY-NAME: " ++ show x ++ " in module " ++ show (F.symbol name)
   x         = val lx
   needsQual = not (isWiredIn lx)

 -}

makeRecordSelectorSigs :: Env -> ModName -> [(Ghc.DataCon, Located DataConP)] 
                       -> [(Ghc.Var, LocSpecType)]
makeRecordSelectorSigs env name dcs = concatMap makeOne dcs
  where
  makeOne (dc, Loc l l' dcp)
    | null fls                    --    no field labels
    || any (isFunTy . snd) args   -- OR function-valued fields
    || dcpIsGadt dcp              -- OR GADT style datcon
    = []
    | otherwise 
    = zip fs ts
    where
      fls = Ghc.dataConFieldLabels dc
      fs  = resolveNamedVar env name . Ghc.flSelector <$> fls 
      ts :: [ LocSpecType ]
      ts = [ Loc l l' (mkArrow (makeRTVar <$> freeTyVars dcp) [] (freeLabels dcp)
                                 [] [(z, res, mempty)]
                                 (dropPreds (F.subst su t `RT.strengthen` mt)))
             | (x, t) <- reverse args -- NOTE: the reverse here is correct
             , let vv = rTypeValueVar t
               -- the measure singleton refinement, eg `v = getBar foo`
             , let mt = RT.uReft (vv, F.PAtom F.Eq (F.EVar vv) (F.EApp (F.EVar x) (F.EVar z)))
             ]
  
      su   = F.mkSubst [ (x, F.EApp (F.EVar x) (F.EVar z)) | x <- fst <$> args ]
      args = tyArgs dcp
      z    = F.notracepp ("makeRecordSelectorSigs:" ++ show args) "lq$recSel"
      res  = dropPreds (tyRes dcp)
  
      -- FIXME: this is clearly imprecise, but the preds in the DataConP seem
      -- to be malformed. If we leave them in, tests/pos/kmp.hs fails with
      -- a malformed predicate application. Niki, help!!
      dropPreds = fmap (\(MkUReft r _ps ss) -> MkUReft r mempty ss)
