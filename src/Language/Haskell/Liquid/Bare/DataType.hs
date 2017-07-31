{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Language.Haskell.Liquid.Bare.DataType
  ( makeConTypes
  , makeTyConEmbeds
  , makeRecordSelectorSigs
  , dataConSpec
  , meetDataConSpec
  , makeNumericInfo
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

import qualified Control.Exception                      as Ex
import qualified Data.List                              as L
import qualified Data.HashMap.Strict                    as M

import qualified Language.Fixpoint.Types                as F -- ({- tracepp, -} mappendFTC, Symbol, TCEmb, mkSubst, Expr(..), Brel(..), subst, symbolNumInfoFTyCon, dummyPos)
import qualified Language.Haskell.Liquid.GHC.Misc       as GM -- (sourcePosSrcSpan, sourcePos2SrcSpan, symbolTyVar)--
import           Language.Haskell.Liquid.Types.PredType (dataConPSpecType)
import qualified Language.Haskell.Liquid.Types.RefType  as RT
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.Meet
import           Language.Fixpoint.Misc                 (mapFst, groupList, mapSnd)
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.WiredIn

import qualified Language.Haskell.Liquid.Measure        as Ms

import           Language.Haskell.Liquid.Bare.Env
import           Language.Haskell.Liquid.Bare.Lookup
import           Language.Haskell.Liquid.Bare.OfType

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
makeDataDecl :: Config -> F.TCEmb TyCon -> DataDecl -> [(DataCon, DataConP)]
             -> Maybe F.DataDecl
makeDataDecl cfg tce dd ctors
  | exactDC cfg = F.tracepp "makeDataDecl" $ Just $ F.DDecl
    { F.ddTyCon = F.symbolFTycon    $ tycName   dd
    , F.ddVars  = length            $ tycTyVars dd
    , F.ddCtors = makeDataCtor tce <$> ctors
    }
  | otherwise   = Nothing

-- HEREHEREHERE -- makeDataConCtor
-- we need to POST-PROCESS the 'Sort' so that:
-- 1. The poly tyvars are replaced with debruijn
--    versions e.g. 'List a_a1m' becomes 'List @(1)'
-- 2. The "self" type is replaced with just itself
--    (i.e. without any type applications.)

makeDataCtor :: F.TCEmb TyCon -> (DataCon, DataConP) -> F.DataCtor
makeDataCtor tce (d, dp) = F.DCtor
  { F.dcName   = GM.namedLocSymbol d
  , F.dcFields = makeDataField tce su . mapFst loc <$> reverse (tyArgs dp)
  }
  where
    su         = zip as [0..]
    as         = rtyVarUniqueSymbol <$> freeTyVars dp
    loc        = Loc (dc_loc dp) (dc_locE dp)


makeDataField :: F.TCEmb TyCon -> [(F.Symbol, Int)] -> (F.LocSymbol, SpecType)
              -> F.DataField
makeDataField tce su (x, t) = F.DField
  { F.dfName = x
  , F.dfSort = F.tracepp ("MAKEDATAFIELD: " ++ showpp t)
                 $ F.substVars su
                 $ RT.rTypeSort tce t
  }

--------------------------------------------------------------------------------
-- | Bare Predicate: DataCon Definitions ---------------------------------------
--------------------------------------------------------------------------------
makeConTypes
  :: Config
  -> F.TCEmb TyCon
  -> (ModName, Ms.Spec ty bndr)
  -> BareM ( [(TyCon, TyConP, Maybe F.DataDecl)]
           , [[(DataCon, Located DataConP)]]   )
makeConTypes cfg tce (name, spec) = inModule name $
  makeConTypes' cfg tce (Ms.dataDecls spec) (Ms.dvariance spec)

makeConTypes' :: Config -> F.TCEmb TyCon -> [DataDecl] -> [(LocSymbol, [Variance])]
              -> BareM ( [(TyCon, TyConP, Maybe F.DataDecl)]
                       , [[(DataCon, Located DataConP)]])
makeConTypes' cfg tce dcs vdcs = unzip <$> mapM (uncurry (ofBDataDecl cfg tce)) (group dcs vdcs)
  where
    _msg                     = F.showpp (tycName <$> dcs)
    group ds vs              = merge (L.sort ds) (L.sortBy (\x y -> compare (fst x) (fst y)) vs)

    merge (d:ds) (v:vs)
      | tycName d == fst v = (Just d, Just v)  : merge ds vs
      | tycName d <  fst v = (Just d, Nothing) : merge ds (v:vs)
      | otherwise          = (Nothing, Just v) : merge (d:ds) vs
    merge []     vs        = ((Nothing,) . Just) <$> vs
    merge ds     []        = ((,Nothing) . Just) <$> ds

dataConSpec :: [(DataCon, DataConP)] -> [(Var, SpecType)]
dataConSpec x = [ (v, t) | (v, (_, t)) <- dataConSpec' x ]

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

checkDataDeclFields ::  (LocSymbol, [(F.Symbol, BareType)]) -> BareM (LocSymbol, [(F.Symbol, BareType)])
checkDataDeclFields (lc, xts)
  | x : _ <- dups = Ex.throw (err lc x :: UserError)
  | otherwise     = return (lc, xts)
    where
      dups        = [ x | (x, ts) <- groupList xts, 2 <= length ts ]

      err lc x    = ErrDupField (GM.sourcePosSrcSpan $ loc lc) (pprint $ val lc) (pprint x)

-- FIXME: ES: why the maybes?
ofBDataDecl :: Config
            -> F.TCEmb TyCon
            -> Maybe DataDecl
            -> (Maybe (LocSymbol, [Variance]))
            -> BareM ((TyCon, TyConP, Maybe F.DataDecl), [(DataCon, Located DataConP)])
ofBDataDecl cfg tce (Just dd@(D tc as ps ls cts0 _ sfun)) maybe_invariance_info
  = do πs            <- mapM ofBPVar ps
       tc'           <- lookupGhcTyCon "ofBDataDecl" tc
       cts           <- mapM checkDataDeclFields cts0
       cts'          <- mapM (ofBDataCon lc lc' tc' αs ps ls πs) cts
       let tys        = [t | (_, dcp) <- cts', (_, t) <- tyArgs dcp]
       let initmap    = zip (RT.uPVar <$> πs) [0..]
       let varInfo    = L.nub $  concatMap (getPsSig initmap True) tys
       let defPs      = varSignToVariance varInfo <$> [0 .. (length πs - 1)]
       let (tvi, pvi) = f defPs
       let tcp        = TyConP lc αs πs ls tvi pvi sfun
       let adt        = makeDataDecl cfg tce dd cts'
       return ((tc', tcp, adt), (mapSnd (Loc lc lc') <$> cts'))
    where
       αs          = RTV . GM.symbolTyVar <$> as
       n           = length αs
       lc          = loc  tc
       lc'         = locE tc
       f defPs     = case maybe_invariance_info of
                      { Nothing -> ([], defPs);
                        Just (_,is) -> (take n is, if null (drop n is) then defPs else (drop n is))}

ofBDataDecl _ _ Nothing (Just (tc, is))
  = do tc'        <- lookupGhcTyCon "ofBDataDecl" tc
       return ((tc', TyConP srcpos [] [] [] tcov tcontr Nothing, Nothing), [])
  where
    (tcov, tcontr) = (is, [])
    srcpos = F.dummyPos "LH.DataType.Variance"

ofBDataDecl _ _ Nothing Nothing
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
ofBDataCon :: SourcePos
           -> SourcePos
           -> TyCon
           -> [RTyVar]
           -> [PVar BSort]
           -> [F.Symbol]
           -> [PVar RSort]
           -> (LocSymbol, [(F.Symbol, BareType)])
           -> BareM (DataCon, DataConP)
ofBDataCon l l' tc αs ps ls πs (c, xts)
  = do c'      <- lookupGhcDataCon c
       ts'     <- mapM (mkSpecType' l ps) ts
       let cs   = map RT.ofType (dataConStupidTheta c')
       let t0   = RT.rApp tc rs (rPropP [] . pdVarReft <$> πs) mempty
       return   $ (c', DataConP l αs πs ls cs (reverse (zip xs ts')) t0 l')
    where
       (xs, ts) = unzip xts
       rs       = [RT.rVar α | RTV α <- αs]


makeTyConEmbeds :: (ModName,Ms.Spec ty bndr) -> BareM (F.TCEmb TyCon)
makeTyConEmbeds (mod, spec)
  = inModule mod $ makeTyConEmbeds' $ Ms.embeds spec

makeTyConEmbeds' :: F.TCEmb LocSymbol -> BareM (F.TCEmb TyCon)
makeTyConEmbeds' z = M.fromList <$> mapM tx (M.toList z)
  where
    tx (c, y) = (, y) <$> lookupGhcTyCon "makeTyConEmbeds'" c

makeRecordSelectorSigs :: [(DataCon, Located DataConP)] -> BareM [(Var, LocSpecType)]
makeRecordSelectorSigs dcs = concat <$> mapM makeOne dcs
  where
  makeOne (dc, Loc l l' dcp)
    | null (dataConFieldLabels dc)
    -- do not make record selectors for data cons with functional arguments
    || any (isFunTy . snd) args
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

    su   = F.mkSubst $ [ (x, F.EApp (F.EVar x) (F.EVar z)) | x <- xs ]
    args = tyArgs dcp
    xs   = map fst args
    z    = "lq$recSel"
    res  = dropPreds (tyRes dcp)

    -- FIXME: this is clearly imprecise, but the preds in the DataConP seem
    -- to be malformed. If we leave them in, tests/pos/kmp.hs fails with
    -- a malformed predicate application. Niki, help!!
    dropPreds = fmap (\(MkUReft r _ps ss) -> MkUReft r mempty ss)
