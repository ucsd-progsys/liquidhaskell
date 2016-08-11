{-# LANGUAGE OverloadedStrings #-}

module Language.Haskell.Liquid.WiredIn
       ( propType
       , propTyCon
       , hpropTyCon
       , pdVarReft
       , wiredTyCons, wiredDataCons
       , wiredSortedSyms

       -- | Constants for automatic proofs
       , dictionaryVar, dictionaryTyVar, dictionaryBind
       , proofTyConName, combineProofsName
       ) where

import Prelude                                hiding (error)
import Var

import Language.Haskell.Liquid.Types
import Language.Fixpoint.Misc           (mapSnd)
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.Types.Variance
import Language.Haskell.Liquid.Types.PredType



import Language.Fixpoint.Types
import qualified Language.Fixpoint.Types as F

import BasicTypes
import DataCon
import TyCon
import TysWiredIn

import TypeRep
import CoreSyn



wiredSortedSyms :: [(Symbol, Sort)]
wiredSortedSyms = [(pappSym n, pappSort n) | n <- [1..pappArity]]

-----------------------------------------------------------------------
-- | LH Primitive TyCons ----------------------------------------------
-----------------------------------------------------------------------

dictionaryVar :: Var
dictionaryVar   = stringVar "tmp_dictionary_var" (ForAllTy dictionaryTyVar $ TyVarTy dictionaryTyVar)

dictionaryTyVar :: TyVar
dictionaryTyVar = stringTyVar "da"

dictionaryBind :: Bind Var
dictionaryBind = Rec [(v, Lam a $ App (Var v) (Type $ TyVarTy a))]
  where
   v = dictionaryVar
   a = dictionaryTyVar



-----------------------------------------------------------------------
-- | LH Primitive TyCons ----------------------------------------------
-----------------------------------------------------------------------


combineProofsName :: String
combineProofsName = "combineProofs"

proofTyConName :: Symbol
proofTyConName = "Proof"

propTyCon, hpropTyCon :: TyCon


{- ATTENTION: Uniques should be different when defining TyCons
   otherwise the TyCons are equal and they will all resolve to
   bool in fixpoint, as propTyCon is a bool
 -}

propTyCon  = symbolTyCon 'w' 25 propConName
hpropTyCon = symbolTyCon 'w' 26 hpropConName

-----------------------------------------------------------------------
-- | LH Primitive Types ----------------------------------------------
-----------------------------------------------------------------------

propType :: Reftable r => RRType r
propType = RApp (RTyCon propTyCon [] defaultTyConInfo) [] [] mempty

--------------------------------------------------------------------
------ Predicate Types for WiredIns --------------------------------
--------------------------------------------------------------------

maxArity :: Arity
maxArity = 7

wiredTyCons :: [(TyCon, TyConP)]
wiredTyCons     = fst wiredTyDataCons

wiredDataCons :: [(DataCon, Located DataConP)]
wiredDataCons   = snd wiredTyDataCons

wiredTyDataCons :: ([(TyCon, TyConP)] , [(DataCon, Located DataConP)])
wiredTyDataCons = (concat tcs, mapSnd dummyLoc <$> concat dcs)
  where
    (tcs, dcs)  = unzip $ listTyDataCons : map tupleTyDataCons [2..maxArity]

listTyDataCons :: ([(TyCon, TyConP)] , [(DataCon, DataConP)])
listTyDataCons   = ( [(c, TyConP [RTV tyv] [p] [] [Covariant] [Covariant] (Just fsize))]
                   , [(nilDataCon, DataConP l0 [RTV tyv] [p] [] [] [] lt l0)
                   , (consDataCon, DataConP l0 [RTV tyv] [p] [] [] cargs  lt l0)])
    where
      l0         = dummyPos "LH.Bare.listTyDataCons"
      c          = listTyCon
      [tyv]      = tyConTyVarsDef c
      t          = rVar tyv :: RSort
      fld        = "fldList"
      x          = "head"
      xs         = "tail"
      p          = PV "p" (PVProp t) (vv Nothing) [(t, fld, EVar fld)]
      px         = pdVarReft $ PV "p" (PVProp t) (vv Nothing) [(t, fld, EVar x)]
      lt         = rApp c [xt] [rPropP [] $ pdVarReft p] mempty
      xt         = rVar tyv
      xst        = rApp c [RVar (RTV tyv) px] [rPropP [] $ pdVarReft p] mempty
      cargs      = [(xs, xst), (x, xt)]
      fsize z    = mkEApp (dummyLoc "len") [EVar z]

tupleTyDataCons :: Int -> ([(TyCon, TyConP)] , [(DataCon, DataConP)])
tupleTyDataCons n = ( [(c, TyConP (RTV <$> tyvs) ps [] tyvarinfo pdvarinfo Nothing)]
                    , [(dc, DataConP l0 (RTV <$> tyvs) ps [] []  cargs  lt l0)])
  where
    tyvarinfo     = replicate n     Covariant
    pdvarinfo     = replicate (n-1) Covariant
    l0            = dummyPos "LH.Bare.tupleTyDataCons"
    c             = tupleTyCon BoxedTuple n
    dc            = tupleCon BoxedTuple n
    tyvs@(tv:tvs) = tyConTyVarsDef c
    (ta:ts)       = (rVar <$> tyvs) :: [RSort]
    flds          = mks "fld_Tuple"
    fld           = "fld_Tuple"
    x1:xs         = mks ("x_Tuple" ++ show n)
    ps            = mkps pnames (ta:ts) ((fld, EVar fld) : zip flds (EVar <$> flds))
    ups           = uPVar <$> ps
    pxs           = mkps pnames (ta:ts) ((fld, EVar x1) : zip flds (EVar <$> xs))
    lt            = rApp c (rVar <$> tyvs) (rPropP [] . pdVarReft <$> ups) mempty
    xts           = zipWith (\v p -> RVar (RTV v) (pdVarReft p)) tvs pxs
    cargs         = reverse $ (x1, rVar tv) : zip xs xts
    pnames        = mks_ "p"
    mks  x        = (\i -> symbol (x++ show i)) <$> [1..n]
    mks_ x        = (\i -> symbol (x++ show i)) <$> [2..n]


pdVarReft :: PVar t -> UReft Reft
pdVarReft = (\p -> MkUReft mempty p mempty) . pdVar

mkps :: [Symbol]
     -> [t] -> [(Symbol, F.Expr)] -> [PVar t]
mkps ns (t:ts) ((f,x):fxs) = reverse $ mkps_ ns ts fxs [(t, f, x)] []
mkps _  _      _           = panic Nothing "Bare : mkps"

mkps_ :: [Symbol]
      -> [t]
      -> [(Symbol, F.Expr)]
      -> [(t, Symbol, F.Expr)]
      -> [PVar t]
      -> [PVar t]
mkps_ []     _       _          _    ps = ps
mkps_ (n:ns) (t:ts) ((f, x):xs) args ps = mkps_ ns ts xs (a:args) (p:ps)
  where
    p                                   = PV n (PVProp t) (vv Nothing) args
    a                                   = (t, f, x)
mkps_ _     _       _          _    _ = panic Nothing "Bare : mkps_"
