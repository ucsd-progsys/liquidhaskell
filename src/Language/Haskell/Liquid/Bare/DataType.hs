{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Language.Haskell.Liquid.Bare.DataType
  ( -- * Constructors
    makeDataDecls
  , makeConTypes
  , makeTyConEmbeds
  , makeRecordSelectorSigs
  , meetDataConSpec
  , makeNumericInfo

  , DataConMap
  , dataConMap

    -- * Tests
  -- , isPropDecl
  -- , qualifyDataDecl
  ) where

import           DataCon
import           Name                                   (getSrcSpan)
import           Prelude                                hiding (error)
import           SrcLoc                                 (SrcSpan)
import           Text.Parsec
import           TyCon                                  hiding (tyConName)
import           Var
import           InstEnv
import           Class
import           Data.Maybe
import           Language.Haskell.Liquid.GHC.TypeRep

import           Control.Monad                          (when) -- , (>=>))
import           Control.Monad.State                    (gets)
import qualified Control.Exception                      as Ex
import qualified Data.List                              as L
import qualified Data.HashMap.Strict                    as M

import qualified Language.Fixpoint.Types.Visitor        as V
import qualified Language.Fixpoint.Types                as F
import qualified Language.Haskell.Liquid.GHC.Misc       as GM -- (sourcePosSrcSpan, sourcePos2SrcSpan, symbolTyVar)--
import           Language.Haskell.Liquid.Types.PredType (dataConPSpecType)
import qualified Language.Haskell.Liquid.Types.RefType  as RT
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.Meet
import qualified Language.Fixpoint.Misc                 as Misc
import qualified Language.Haskell.Liquid.Misc           as Misc
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.WiredIn

import qualified Language.Haskell.Liquid.Measure        as Ms

import qualified Language.Haskell.Liquid.Bare.Misc      as GM
import           Language.Haskell.Liquid.Bare.Env
import           Language.Haskell.Liquid.Bare.Lookup
import           Language.Haskell.Liquid.Bare.OfType
-- import           Text.Printf                     (printf)
-- import           Debug.Trace (trace)

makeNumericInfo :: Maybe [ClsInst] -> F.TCEmb TyCon -> F.TCEmb TyCon
makeNumericInfo Nothing x   = x
makeNumericInfo (Just is) x = foldl makeNumericInfoOne x is

makeNumericInfoOne :: F.TCEmb TyCon -> ClsInst -> F.TCEmb TyCon
makeNumericInfoOne m is
  | isFracCls $ classTyCon $ is_cls is, Just tc <- instanceTyCon is
  = M.insertWith (flip F.mappendFTC) tc (ftc tc True True) m
  | isNumCls $ classTyCon $ is_cls is, Just tc <- instanceTyCon is
  = M.insertWith (flip F.mappendFTC) tc (ftc tc True False) m
  | otherwise
  = m
  where
    ftc c = F.symbolNumInfoFTyCon (dummyLoc $ RT.tyConName c)

instanceTyCon :: ClsInst -> Maybe TyCon
instanceTyCon = go . is_tys
  where
    go [TyConApp c _] = Just c
    go _              = Nothing

--------------------------------------------------------------------------------
-- | Create Fixpoint DataDecl from LH DataDecls --------------------------------
--------------------------------------------------------------------------------

-- | A 'DataPropDecl' is associated with a (`TyCon` and) `DataDecl`, and defines the
--   sort of relation that is established by terms of the given `TyCon`.
--   A 'DataPropDecl' say, 'pd' is associated with a 'dd' of type 'DataDecl' when
--   'pd' is the `SpecType` version of the `BareType` given by `tycPropTy dd`.

type DataPropDecl = (DataDecl, Maybe SpecType)

makeDataDecls :: Config -> F.TCEmb TyCon
              -> [(ModName, TyCon, DataPropDecl)]
              -> [(DataCon, Located DataConP)]
              -> [F.DataDecl]
makeDataDecls cfg tce tds ds
  | makeDecls = [ makeFDataDecls tce tc dd ctors
                | (tc, (dd, ctors)) <- groupDataCons tds' (F.tracepp "makeDataDecls-DATACONS" ds) ]
  | otherwise = []
  where
    makeDecls = exactDC cfg && not (noADT cfg)
    tds'      = indexTyConDecls tds --[ (tc, (d, t)) | (_, tc, (d, t)) <- F.tracepp "makeDataDecls-TYCONS" tds ]

-- [NOTE:Orphan-TyCons]

{- | 'indexTyConDecls' will prune duplicate 'TyCon' definitions, as follows:

      Let the "home" of a 'TyCon' be the module where it is defined.
      There are three kinds of 'DataDecl' definitions:

      1. A  "home"-definition is one that belongs to its home module,
      2. An "orphan"-definition is one that belongs to some non-home module.

      A 'DataUser' definition MUST be a "home" definition
          - otherwise you can avoid importing the definition
            and hence, unsafely pass its invariants!

      So, 'resolveTyConDecls' implements the following protocol:

      (a) If there is a "Home" definition, then use it, and IGNORE others.

      (b) If there are ONLY "orphan" definitions, PICK ANY;
          they must all be 'DataReflected' and hence, equivalent.

-}
indexTyConDecls :: [(ModName, TyCon, DataPropDecl)] -> [(TyCon, (ModName, DataPropDecl))]
indexTyConDecls mtds = [(tc, (m, d)) | (tc, mds) <- M.toList tcDecls
                                     , let (m, d) = resolveTyConDecls tc mds ]
  where
    tcDecls          = Misc.group [ (tc, (m, d)) | (m, tc, d) <- mtds ]

-- | See [NOTE:Orphan-TyCons], the below function tells us which of (possibly many)
--   DataDecls to use.
resolveTyConDecls :: TyCon -> Misc.ListNE (ModName, DataPropDecl) -> (ModName, DataPropDecl)
resolveTyConDecls tc mds
  | Just (m, d) <- homeDef = (m, d)
  | otherwise              = head mds
  where
    homeDef                = L.find ((tcHome ==) . F.symbol . fst) mds
    tcHome                 = GM.takeModuleNames (F.symbol tc)

groupDataCons :: [(TyCon, (ModName, DataPropDecl))]
              -> [(DataCon, Located DataConP)]
              -> [(TyCon, (DataPropDecl, [(DataCon, DataConP)]))]
groupDataCons tds ds = [ (tc, (d, dds')) | (tc, ((m, d), dds)) <- tcDataCons
                                         , let dds' = filter (isResolvedDataConP m . snd) dds
                       ]
  where
    tcDataCons       = M.toList $ M.intersectionWith (,) declM ctorM
    declM            = M.fromList tds
    ctorM            = Misc.group [(dataConTyCon d, (d, val dp)) | (d, dp) <- ds]

isResolvedDataConP :: ModName -> DataConP -> Bool
isResolvedDataConP m dp = F.symbol m == dcpModule dp

_groupDataCons :: [(TyCon, DataPropDecl)]
              -> [(DataCon, Located DataConP)]
              -> [(TyCon, (DataPropDecl, [(DataCon, DataConP)]))]
_groupDataCons tds ds = M.toList $ M.intersectionWith (,) declM ctorM
  where
    declM             = M.fromList tds
    ctorM             = Misc.group [(dataConTyCon d, (d, val dp)) | (d, dp) <- ds]


makeFDataDecls :: F.TCEmb TyCon -> TyCon -> DataPropDecl -> [(DataCon, DataConP)]
               -> F.DataDecl
makeFDataDecls tce tc dd ctors = makeDataDecl tce tc (fst dd) ctors
                               -- ++ maybeToList (makePropDecl tce tc dd) -- TODO: AUTO-INDPRED

makeDataDecl :: F.TCEmb TyCon -> TyCon -> DataDecl -> [(DataCon, DataConP)]
             -> F.DataDecl
makeDataDecl tce tc dd ctors
  = F.DDecl
      { F.ddTyCon = ftc
      , F.ddVars  = length                $  tycTyVars dd
      , F.ddCtors = makeDataCtor tce ftc <$> ctors
      }
  where
    ftc = F.symbolFTycon (tyConLocSymbol tc dd)

tyConLocSymbol :: TyCon -> DataDecl -> LocSymbol
tyConLocSymbol tc dd = F.atLoc (tycName dd) (F.symbol tc)

-- [NOTE:ADT] We need to POST-PROCESS the 'Sort' so that:
-- 1. The poly tyvars are replaced with debruijn
--    versions e.g. 'List a_a1m' becomes 'List @(1)'
-- 2. The "self" type is replaced with just itself
--    (i.e. without any type applications.)

makeDataCtor :: F.TCEmb TyCon -> F.FTycon -> (DataCon, DataConP) -> F.DataCtor
makeDataCtor tce c (d, dp) = F.DCtor
  { F.dcName    = GM.namedLocSymbol d
  , F.dcFields  = makeDataFields tce c as xts
  }
  where
    as          = freeTyVars dp
    xts         = [ (fld x, t) | (x, t) <- reverse (tyArgs dp) ]
    fld         = Loc (dc_loc dp) (dc_locE dp) . fieldName d dp

fieldName :: DataCon -> DataConP -> F.Symbol -> F.Symbol
fieldName d dp x
  | dcpIsGadt dp = F.suffixSymbol (F.symbol d) x
  | otherwise    = x

makeDataFields :: F.TCEmb TyCon -> F.FTycon -> [RTyVar] -> [(F.LocSymbol, SpecType)]
               -> [F.DataField]
makeDataFields tce c as xts = [ F.DField x (fSort t) | (x, t) <- xts]
  where
    su                      = zip (rtyVarUniqueSymbol <$> as) [0..]
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
makeConTypes
  :: (ModName, Ms.Spec ty bndr)
  -> BareM ( [(ModName, TyCon, TyConP, Maybe DataPropDecl)]
           , [[(DataCon, Located DataConP)]]   )
makeConTypes (name, spec) = inModule name $
  makeConTypes' name (Ms.dataDecls spec) (Ms.dvariance spec)

makeConTypes' :: ModName -> [DataDecl] -> [(LocSymbol, [Variance])]
              -> BareM ( [(ModName, TyCon, TyConP, Maybe DataPropDecl)]
                       , [[(DataCon, Located DataConP)]])
makeConTypes' name dcs vdcs = do
  dcs' <- canonizeDecls dcs
  unzip <$> mapM (uncurry (ofBDataDecl name)) (groupVariances dcs' vdcs)

-- | 'canonizeDecls ds' returns a subset of 'ds' where duplicates, e.g. arising
--   due to automatic lifting (via 'makeHaskellDataDecls'). We require that the
--   lifted versions appear LATER in the input list, and always use those instead
--   of the unlifted versions.

canonizeDecls :: [DataDecl] -> BareM [DataDecl]
canonizeDecls = Misc.nubHashLastM key
  where
    key       = fmap F.symbol . lookupGhcTyCon "canonizeDecls" . tycName

groupVariances :: [DataDecl] -> [(LocSymbol, [Variance])]
               -> [(Maybe DataDecl, Maybe (LocSymbol, [Variance]))]
groupVariances dcs vdcs    =  merge (L.sort dcs) (L.sortBy (\x y -> compare (fst x) (fst y)) vdcs)
  where
    merge (d:ds) (v:vs)
      | tycName d == fst v = (Just d, Just v)  : merge ds vs
      | tycName d <  fst v = (Just d, Nothing) : merge ds (v:vs)
      | otherwise          = (Nothing, Just v) : merge (d:ds) vs
    merge []     vs        = ((Nothing,) . Just) <$> vs
    merge ds     []        = ((,Nothing) . Just) <$> ds

dataConSpec' :: [(DataCon, DataConP)] -> [(Var, (SrcSpan, SpecType))]
dataConSpec' dcs = concatMap tx dcs
  where
    tx (a, b)    = [ (x, (sspan b, t)) | (x, t) <- RT.mkDataConIdsTy (a, dataConPSpecType a b) ]
    sspan z      = GM.sourcePos2SrcSpan (dc_loc z) (dc_locE z)

meetDataConSpec :: [(Var, SpecType)] -> [(DataCon, DataConP)] -> [(Var, SpecType)]
meetDataConSpec xts dcs  = M.toList $ snd <$> L.foldl' upd dcm0 xts
  where
    dcm0                 = M.fromList $ dataConSpec' dcs
    meetX x t (sp', t')  = meetVarTypes (pprint x) (getSrcSpan x, t) (sp', t')
    upd dcm (x, t)       = M.insert x (getSrcSpan x, tx') dcm
                             where
                               tx' = maybe t (meetX x t) (M.lookup x dcm)

checkDataCtor :: DataCtor -> BareM DataCtor
checkDataCtor d@(DataCtor lc xts _)
  | x : _ <- dups = Ex.throw (err lc x :: UserError)
  | otherwise     = return d
    where
      dups        = [ x | (x, ts) <- Misc.groupList xts, 2 <= length ts ]
      err lc x    = ErrDupField (GM.sourcePosSrcSpan $ loc lc) (pprint $ val lc) (pprint x)

-- | 'checkDataDecl' checks that the supplied DataDecl is indeed a refinement
--   of the GHC TyCon. We just check that the right tyvars are supplied
--   as errors in the names and types of the constructors will be caught
--   elsewhere. [e.g. tests/errors/BadDataDecl.hs]

checkDataDecl :: TyCon -> DataDecl -> Bool
checkDataDecl c d = (cN == dN || null (tycDCons d))
  where
    -- _msg          = printf "checkDataDecl: c = %s, cN = %d, dN = %d" (show c) cN dN
    cN            = length (GM.tyConTyVarsDef c)
    dN            = length (tycTyVars         d)


-- FIXME: ES: why the maybes?
ofBDataDecl :: ModName
            -> Maybe DataDecl
            -> (Maybe (LocSymbol, [Variance]))
            -> BareM ((ModName, TyCon, TyConP, Maybe DataPropDecl), [(DataCon, Located DataConP)])
ofBDataDecl name (Just dd@(D tc as ps ls cts0 _ sfun pt _)) maybe_invariance_info
  = do πs            <- mapM ofBPVar ps
       tc'           <- lookupGhcTyCon "ofBDataDecl" tc
       when (not $ checkDataDecl tc' dd) (Ex.throw err)
       cts           <- mapM checkDataCtor cts0
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
       err         = ErrBadData (GM.fSrcSpan tc) (pprint tc) "Mismatch in number of type variables" :: UserError
       αs          = RTV . GM.symbolTyVar <$> as
       n           = length αs
       lc          = loc  tc
       lc'         = locE tc
       f defPs     = case maybe_invariance_info of
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
ofBDataCtor name l l' tc αs ps ls πs (DataCtor c xts res) = do
  c'           <- lookupGhcDataCon c
  ts'          <- mapM (mkSpecType' l ps) ts
  res'         <- mapM (mkSpecType' l ps) res
  let cs        = RT.ofType <$> dataConStupidTheta c'
  let t0'       = fromMaybe t0 res'
  cfg          <- gets beConfig
  let (yts, ot) = F.notracepp "OFBDataCTOR" $ qualifyDataCtor (exactDC cfg && not isGadt) name dLoc (zip xs ts', t0')
  let zts       = zipWith (normalizeField c') [1..] (reverse yts)
  return          (c', DataConP l αs πs ls cs zts ot isGadt (F.symbol name) l')
  where
    (xs, ts) = unzip xts
    rs       = [RT.rVar α | RTV α <- αs]
    t0       = RT.rApp tc rs (rPropP [] . pdVarReft <$> πs) mempty
    isGadt   = isJust res
    dLoc     = F.Loc l l' ()

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
 | needsQual = (Just x, F.notracepp msg $ qualifyName name x)
 | otherwise = (Nothing, x)
 where
   msg       = "QUALIFY-NAME: " ++ show x ++ " in module " ++ show (F.symbol name)
   x         = val lx
   needsQual = not (isWiredIn lx)

qualifyName :: ModName -> F.Symbol -> F.Symbol
qualifyName n = GM.qualifySymbol nSym
 where
   nSym       = F.symbol n

makeTyConEmbeds :: (ModName,Ms.Spec ty bndr) -> BareM (F.TCEmb TyCon)
makeTyConEmbeds (mod, spec)
  = inModule mod $ makeTyConEmbeds' $ Ms.embeds spec

makeTyConEmbeds' :: F.TCEmb LocSymbol -> BareM (F.TCEmb TyCon)
makeTyConEmbeds' z = M.fromList <$> mapM tx (M.toList z)
  where
    tx (c, y) = (, y) <$> lookupGhcTyCon "makeTyConEmbeds'" c

makeRecordSelectorSigs :: [(DataCon, Located DataConP)] -> BareM [(Var, LocSpecType)]
makeRecordSelectorSigs dcs = F.notracepp "makeRecordSelectorSigs" <$> (concat <$> mapM makeOne dcs)
  where
  makeOne (dc, Loc l l' dcp)
    | null (dataConFieldLabels dc)  -- no field labels OR
      || any (isFunTy . snd) args   -- OR function-valued fields
      || dcpIsGadt dcp              -- OR GADT style datcon
    = return []
    | otherwise = do
        fs <- mapM lookupGhcVar (dataConFieldLabels dc)
        return $ zip fs ts
    where
    ts :: [ LocSpecType ]
    ts = [ Loc l l' (mkArrow (makeRTVar <$> freeTyVars dcp) [] (freeLabels dcp)
                               [(z, res, mempty)]
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
