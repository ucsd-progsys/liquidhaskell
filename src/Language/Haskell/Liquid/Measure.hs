{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ConstraintKinds        #-}

module Language.Haskell.Liquid.Measure (
  -- * Specifications
    Spec (..)
  , MSpec (..)

  -- * Type Aliases
  , BareSpec
  , BareMeasure
  , SpecMeasure

  -- * Constructors
  , mkM, mkMSpec, mkMSpec'
  , dataConTypes
  , defRefType
  , bodyPred
  ) where

import           GHC                                    hiding (Located)
import           Prelude                                hiding (error)
import           Text.PrettyPrint.HughesPJ              hiding ((<>)) 
-- import           Data.Binary                            as B
-- import           GHC.Generics
import qualified Data.HashMap.Strict                    as M
import qualified Data.List                              as L
import qualified Data.Maybe                             as Mb -- (fromMaybe, isNothing)

import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types                hiding (panic, R, DataDecl, SrcSpan, LocSymbol)
import           Language.Haskell.Liquid.GHC.API        as Ghc hiding (Expr, showPpr, panic, (<+>))
import           Language.Haskell.Liquid.GHC.Misc
-- import qualified Language.Haskell.Liquid.Misc as Misc
import           Language.Haskell.Liquid.Types.Types    -- hiding (GhcInfo(..), GhcSpec (..))
import           Language.Haskell.Liquid.Types.RefType
-- import           Language.Haskell.Liquid.Types.Variance
-- import           Language.Haskell.Liquid.Types.Bounds
import           Language.Haskell.Liquid.Types.Specs hiding (BareSpec)
import           Language.Haskell.Liquid.UX.Tidy

-- /FIXME/: This needs to be removed once the port to the new API is complete.
type BareSpec = Spec LocBareType LocSymbol

mkM ::  LocSymbol -> ty -> [Def ty bndr] -> MeasureKind -> UnSortedExprs -> Measure ty bndr
mkM name typ eqns kind u
  | all ((name ==) . measure) eqns
  = M name typ eqns kind u
  | otherwise
  = panic Nothing $ "invalid measure definition for " ++ show name

mkMSpec' :: Symbolic ctor => [Measure ty ctor] -> MSpec ty ctor
mkMSpec' ms = MSpec cm mm M.empty []
  where
    cm     = groupMap (symbol . ctor) $ concatMap msEqns ms
    mm     = M.fromList [(msName m, m) | m <- ms ]

mkMSpec :: [Measure t LocSymbol] -> [Measure t ()] -> [Measure t LocSymbol] -> MSpec t LocSymbol
mkMSpec ms cms ims = MSpec cm mm cmm ims
  where
    cm     = groupMap (val . ctor) $ concatMap msEqns (ms'++ims)
    mm     = M.fromList [(msName m, m) | m <- ms' ]
    cmm    = M.fromList [(msName m, m) | m <- cms ]
    ms'    = checkDuplicateMeasure ms


checkDuplicateMeasure :: [Measure ty ctor] -> [Measure ty ctor]
checkDuplicateMeasure measures
  = case M.toList dups of
      []         -> measures
      (m,ms):_   -> uError $ err' m (msName <$> ms)
    where
      gms        = group [(msName m , m) | m <- measures]
      dups       = M.filter ((1 <) . length) gms
      err' m ms   = ErrDupMeas (fSrcSpan m) (pprint (val m)) (fSrcSpan <$> ms)


dataConTypes :: Bool -> MSpec (RRType Reft) DataCon -> ([(Var, RRType Reft)], [(LocSymbol, RRType Reft)])
dataConTypes allowTC  s = (ctorTys, measTys)
  where
    measTys     = [(msName m, msSort m) | m <- M.elems (measMap s) ++ imeas s]
    ctorTys     = concatMap (makeDataConType allowTC) (notracepp "HOHOH" . snd <$> M.toList (ctorMap s))

makeDataConType :: Bool -> [Def (RRType Reft) DataCon] -> [(Var, RRType Reft)]
makeDataConType _ []
  = []
makeDataConType allowTC ds | Mb.isNothing (dataConWrapId_maybe dc)
  = notracepp _msg [(woId, notracepp _msg $ combineDCTypes "cdc0" t ts)]
  where
    dc   = ctor (head ds)
    woId = dataConWorkId dc
    t    = varType woId
    ts   = defRefType allowTC t <$> ds
    _msg  = "makeDataConType0" ++ showpp (woId, t, ts)

makeDataConType allowTC ds
  = [(woId, extend allowTC loci woRType wrRType), (wrId, extend allowTC loci wrRType woRType)]
  where
    (wo, wr) = L.partition isWorkerDef ds
    dc       = ctor $ head ds
    loci     = loc $ measure $ head ds
    woId     = dataConWorkId dc
    wot      = varType woId
    wrId     = dataConWrapId dc
    wrt      = varType wrId
    wots     = defRefType allowTC wot <$> wo
    wrts     = defRefType allowTC wrt <$> wr

    wrRType  = combineDCTypes "cdc1" wrt wrts
    woRType  = combineDCTypes "cdc2" wot wots


    isWorkerDef def
      -- types are missing for arguments, so definition came from a logical measure
      -- and it is for the worker datacon
      | any Mb.isNothing (snd <$> binds def)
      = True
      | otherwise
      = length (binds def) == length (fst $ splitFunTys $ snd $ splitForAllTys wot)


extend :: Bool
       -> SourcePos
       -> RType RTyCon RTyVar Reft
       -> RRType Reft
       -> RType RTyCon RTyVar Reft
extend allowTC lc t1' t2
  | Just su <- mapArgumens allowTC lc t1 t2
  = t1 `strengthenResult` subst su (Mb.fromMaybe mempty (stripRTypeBase $ resultTy t2))
  | otherwise
  = t1
  where
    t1 = noDummySyms t1'


resultTy :: RType c tv r -> RType c tv r
resultTy = ty_res . toRTypeRep

strengthenResult :: Reftable r => RType c tv r -> r -> RType c tv r
strengthenResult t r = fromRTypeRep $ rep {ty_res = ty_res rep `strengthen` r}
  where
    rep              = toRTypeRep t


noDummySyms :: (OkRT c tv r) => RType c tv r -> RType c tv r
noDummySyms t
  | any isDummy (ty_binds rep)
  = subst su $ fromRTypeRep $ rep{ty_binds = xs'}
  | otherwise
  = t
  where
    rep = toRTypeRep t
    xs' = zipWith (\_ i -> symbol ("x" ++ show i)) (ty_binds rep) [(1::Int)..]
    su  = mkSubst $ zip (ty_binds rep) (EVar <$> xs')

combineDCTypes :: String -> Type -> [RRType Reft] -> RRType Reft
combineDCTypes _msg t ts = L.foldl' strengthenRefTypeGen (ofType t) ts

mapArgumens :: Bool -> SourcePos -> RRType Reft -> RRType Reft -> Maybe Subst
mapArgumens allowTC lc t1 t2 = go xts1' xts2'
  where
    xts1 = zip (ty_binds rep1) (ty_args rep1)
    xts2 = zip (ty_binds rep2) (ty_args rep2)
    rep1 = toRTypeRep t1
    rep2 = toRTypeRep t2

    xts1' = dropWhile canDrop xts1
    xts2' = dropWhile canDrop xts2

    canDrop (_, t) = if allowTC then isEmbeddedClass t else isClassType t || isEqType t

    go xs ys
      | length xs == length ys && and (zipWith (==) (toRSort . snd <$> xts1') (toRSort . snd <$> xts2'))
      = Just $ mkSubst $ zipWith (\y x -> (fst x, EVar $ fst y)) xts1' xts2'
      | otherwise
      = panic (Just $ sourcePosSrcSpan lc) ("The types for the wrapper and worker data constructors cannot be merged\n"
          ++ show t1 ++ "\n" ++ show t2 )

-- should constructors have implicits? probably not
defRefType :: Bool -> Type -> Def (RRType Reft) DataCon -> RRType Reft
defRefType allowTC tdc (Def f dc mt xs body)
                    = generalize $ mkArrow as' [] [] xts t'
  where
    xts             = stitchArgs allowTC (fSrcSpan f) dc xs ts 
    t'              = refineWithCtorBody dc f body t
    t               = Mb.fromMaybe (ofType tr) mt
    (αs, ts, tr)    = splitType tdc
    as              = if Mb.isJust mt then [] else makeRTVar . rTyVar <$> αs
    as'             = zip as (repeat mempty)

splitType :: Type -> ([TyVar],[Type], Type)
splitType t  = (αs, map irrelevantMult ts, tr)
  where
    (αs, tb) = splitForAllTys t
    (ts, tr) = splitFunTys tb

stitchArgs :: (Monoid t1, PPrint a)
           => Bool
           -> SrcSpan
           -> a
           -> [(Symbol, Maybe (RRType Reft))]
           -> [Type]
           -> [(Symbol, RFInfo, RRType Reft, t1)]
stitchArgs allowTC sp dc allXs allTs
  | nXs == nTs         = (g (dummySymbol, Nothing) . ofType <$> pts)
                      ++ zipWith g xs (ofType <$> ts)
  | otherwise          = panicFieldNumMismatch sp dc nXs nTs
    where
      (pts, ts)        = L.partition (\t -> notracepp ("isPredTy: " ++ showpp t) $ (if allowTC then isEmbeddedDictType else Ghc.isEvVarType ) t) allTs
      (_  , xs)        = L.partition (coArg . snd) allXs
      nXs              = length xs
      nTs              = length ts
      g (x, Just t) _  = (x, classRFInfo allowTC, t, mempty)
      g (x, _)      t  = (x, classRFInfo allowTC, t, mempty)
      coArg Nothing    = False
      coArg (Just t)   = (if allowTC then isEmbeddedDictType else Ghc.isEvVarType ). toType False $ t

panicFieldNumMismatch :: (PPrint a, PPrint a1, PPrint a3)
                      => SrcSpan -> a3 -> a1 -> a -> a2
panicFieldNumMismatch sp dc nXs nTs  = panicDataCon sp dc msg
  where
    msg = "Requires" <+> pprint nTs <+> "fields but given" <+> pprint nXs

panicDataCon :: PPrint a1 => SrcSpan -> a1 -> Doc -> a
panicDataCon sp dc d
  = panicError $ ErrDataCon sp (pprint dc) d

refineWithCtorBody :: Outputable a
                   => a
                   -> LocSymbol
                   -> Body
                   -> RType c tv Reft
                   -> RType c tv Reft
refineWithCtorBody dc f body t =
  case stripRTypeBase t of
    Just (Reft (v, _)) ->
      strengthen t $ Reft (v, bodyPred (mkEApp f [eVar v]) body)
    Nothing ->
      panic Nothing $ "measure mismatch " ++ showpp f ++ " on con " ++ showPpr dc


bodyPred ::  Expr -> Body -> Expr
bodyPred fv (E e)    = PAtom Eq fv e
bodyPred fv (P p)    = PIff  fv p
bodyPred fv (R v' p) = subst1 p (v', fv)
