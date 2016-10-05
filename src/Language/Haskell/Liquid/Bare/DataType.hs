{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Language.Haskell.Liquid.Bare.DataType (
    makeConTypes
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
import           TypeRep 


import qualified Data.List                              as L
import qualified Data.HashMap.Strict                    as M

import           Language.Fixpoint.Types                (mappendFTC, Symbol, TCEmb, mkSubst, Expr(..), Brel(..), subst, symbolNumInfoFTyCon)
import           Language.Haskell.Liquid.GHC.Misc       (sourcePos2SrcSpan, symbolTyVar)
import           Language.Haskell.Liquid.Types.PredType (dataConPSpecType)
import           Language.Haskell.Liquid.Types.RefType  (mkDataConIdsTy, ofType, rApp, rVar, strengthen, uPVar, uReft, tyConName)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.Meet
import           Language.Fixpoint.Misc                 (mapSnd)
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.WiredIn

import qualified Language.Haskell.Liquid.Measure        as Ms

import           Language.Haskell.Liquid.Bare.Env
import           Language.Haskell.Liquid.Bare.Lookup
import           Language.Haskell.Liquid.Bare.OfType



makeNumericInfo :: Maybe [ClsInst] -> TCEmb TyCon -> TCEmb TyCon
makeNumericInfo Nothing x   = x 
makeNumericInfo (Just is) x = foldl makeNumericInfoOne x is 

makeNumericInfoOne :: TCEmb TyCon -> ClsInst -> TCEmb TyCon
makeNumericInfoOne m is 
  | isFracCls $ classTyCon $ is_cls is, Just tc <- instanceTyCon is  
  = M.insertWith (flip mappendFTC) tc (ftc tc True True) m 
  | isNumCls $ classTyCon $ is_cls is, Just tc <- instanceTyCon is  
  = M.insertWith (flip mappendFTC) tc (ftc tc True False) m
  | otherwise
  = m 
  where
    ftc c = symbolNumInfoFTyCon (dummyLoc $ tyConName c)

instanceTyCon :: ClsInst -> Maybe TyCon 
instanceTyCon = go . is_tys
  where
    go [TyConApp c _] = Just c 
    go _              = Nothing 

-----------------------------------------------------------------------
-- Bare Predicate: DataCon Definitions --------------------------------
-----------------------------------------------------------------------

makeConTypes
  :: (ModName,Ms.Spec ty bndr)
  -> BareM ([(TyCon,TyConP)],[[(DataCon,Located DataConP)]])
makeConTypes (name,spec) = inModule name $ makeConTypes' (Ms.dataDecls spec) (Ms.dvariance spec)

makeConTypes' :: [DataDecl] -> [(LocSymbol, [Variance])] -> BareM ([(TyCon, TyConP)], [[(DataCon, Located DataConP)]])
makeConTypes' dcs vdcs = unzip <$> mapM (uncurry ofBDataDecl) (group dcs vdcs)
  where
        group ds vs = merge (L.sort ds) (L.sortBy (\x y -> compare (fst x) (fst y)) vs)

        merge (d:ds) (v:vs)
          | tycName d == fst v = (Just d, Just v)  : merge ds vs
          | tycName d <  fst v = (Just d, Nothing) : merge ds (v:vs)
          | otherwise          = (Nothing, Just v) : merge (d:ds) vs
        merge []     vs  = ((Nothing,) . Just) <$> vs
        merge ds     []  = ((,Nothing) . Just) <$> ds

dataConSpec :: [(DataCon, DataConP)] -> [(Var, SpecType)]
dataConSpec x = [ (v, t) | (v, (_, t)) <- dataConSpec' x ]

dataConSpec' :: [(DataCon, DataConP)] -> [(Var, (SrcSpan, SpecType))]
dataConSpec' dcs = concatMap tx dcs
  where
    tx (a, b)    = [ (x, (sspan b, t)) | (x, t) <- mkDataConIdsTy (a, dataConPSpecType a b) ]
    sspan z      = sourcePos2SrcSpan (dc_loc z) (dc_locE z)

meetDataConSpec :: [(Var, SpecType)] -> [(DataCon, DataConP)] -> [(Var, SpecType)]
meetDataConSpec xts dcs  = M.toList $ snd <$> L.foldl' upd dcm0 xts
  where
    dcm0                 = M.fromList $ dataConSpec' dcs
    meetX x t (sp', t')  = meetVarTypes (pprint x) (getSrcSpan x, t) (sp', t')
    upd dcm (x, t)       = M.insert x (getSrcSpan x, tx') dcm
                             where
                               tx' = maybe t (meetX x t) (M.lookup x dcm)


-- FIXME: ES: why the maybes?
ofBDataDecl :: Maybe DataDecl
            -> (Maybe (LocSymbol, [Variance]))
            -> BareM ((TyCon, TyConP), [(DataCon, Located DataConP)])
ofBDataDecl (Just (D tc as ps ls cts _ sfun)) maybe_invariance_info
  = do πs         <- mapM ofBPVar ps
       tc'        <- lookupGhcTyCon tc
       cts'       <- mapM (ofBDataCon lc lc' tc' αs ps ls πs) cts
       let tys     = [t | (_, dcp) <- cts', (_, t) <- tyArgs dcp]
       let initmap = zip (uPVar <$> πs) [0..]
       let varInfo = L.nub $  concatMap (getPsSig initmap True) tys
       let defaultPs = varSignToVariance varInfo <$> [0 .. (length πs - 1)]
       let (tvarinfo, pvarinfo) = f defaultPs
       return ((tc', TyConP αs πs ls tvarinfo pvarinfo sfun), (mapSnd (Loc lc lc') <$> cts'))
    where
       αs          = RTV . symbolTyVar <$> as
       n           = length αs
       lc          = loc  tc
       lc'         = locE tc
       f defaultPs = case maybe_invariance_info of
           {Nothing -> ([], defaultPs);
            Just (_,is) -> (take n is, if null (drop n is) then defaultPs else (drop n is))}


       varSignToVariance varsigns i = case filter (\p -> fst p == i) varsigns of
                                []       -> Invariant
                                [(_, b)] -> if b then Covariant else Contravariant
                                _        -> Bivariant

ofBDataDecl Nothing (Just (tc, is))
  = do tc'        <- lookupGhcTyCon tc
       return ((tc', TyConP [] [] [] tcov tcontr Nothing), [])
  where
    (tcov, tcontr) = (is, [])

ofBDataDecl Nothing Nothing
  = panic Nothing "Bare.DataType.ofBDataDecl called on invalid inputs"

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
  where f = fromMaybe (panic Nothing "Bare.addPs: notfound") . (`L.lookup` m) . uPVar

-- TODO:EFFECTS:ofBDataCon
ofBDataCon :: SourcePos
           -> SourcePos
           -> TyCon
           -> [RTyVar]
           -> [PVar BSort]
           -> [Symbol]
           -> [PVar RSort]
           -> (Located Symbol,[(Symbol,BareType)])
           -> BareM (DataCon,DataConP)
ofBDataCon l l' tc αs ps ls πs (c, xts)
  = do c'      <- lookupGhcDataCon c
       ts'     <- mapM (mkSpecType' l ps) ts
       let cs   = map ofType (dataConStupidTheta c')
       let t0   = rApp tc rs (rPropP [] . pdVarReft <$> πs) mempty
       return   $ (c', DataConP l αs πs ls cs (reverse (zip xs ts')) t0 l')
    where
       (xs, ts) = unzip xts
       rs       = [rVar α | RTV α <- αs]


makeTyConEmbeds :: (ModName,Ms.Spec ty bndr) -> BareM (TCEmb TyCon)
makeTyConEmbeds (mod, spec)
  = inModule mod $ makeTyConEmbeds' $ Ms.embeds spec

makeTyConEmbeds' :: TCEmb (Located Symbol) -> BareM (TCEmb TyCon)
makeTyConEmbeds' z = M.fromList <$> mapM tx (M.toList z)
  where
    tx (c, y) = (, y) <$> lookupGhcTyCon c

makeRecordSelectorSigs :: [(DataCon, Located DataConP)] -> BareM [(Var, Located SpecType)]
makeRecordSelectorSigs dcs = concat <$> mapM makeOne dcs
  where
  makeOne (dc, Loc l l' dcp)
    | null (dataConFieldLabels dc)
    -- do not make record selectors for data cons with functional arguments  
    || any (isFunTy . snd) (args)
    = return []
    | otherwise = do
        fs <- mapM lookupGhcVar (dataConFieldLabels dc)
        return $ zip fs ts  
    where
    ts = [ Loc l l' (mkArrow (makeRTVar <$> freeTyVars dcp) [] (freeLabels dcp)
                               [(z, res, mempty)]
                               (dropPreds (subst su t `strengthen` mt)))
           | (x, t) <- reverse args -- NOTE: the reverse here is correct
           , let vv = rTypeValueVar t
             -- the measure singleton refinement, eg `v = getBar foo`
           , let mt = uReft (vv, PAtom Eq (EVar vv) (EApp (EVar x) (EVar z)))
           ]

    su   = mkSubst $ [ (x, EApp (EVar x) (EVar z)) | x <- xs ]
    args = tyArgs dcp
    xs   = map fst args
    z    = "lq$recSel"
    res  = dropPreds (tyRes dcp)

    -- FIXME: this is clearly imprecise, but the preds in the DataConP seem
    -- to be malformed. If we leave them in, tests/pos/kmp.hs fails with
    -- a malformed predicate application. Niki, help!!
    dropPreds = fmap (\(MkUReft r _ps ss) -> MkUReft r mempty ss)
