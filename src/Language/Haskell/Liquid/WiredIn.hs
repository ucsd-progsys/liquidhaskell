{-# LANGUAGE OverloadedStrings          #-}

module Language.Haskell.Liquid.WiredIn where

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.GhcMisc
import Language.Haskell.Liquid.Variance

import Language.Fixpoint.Names                  (hpropConName, propConName)
import Language.Fixpoint.Types
import Language.Fixpoint.Misc                   (mapSnd)

import BasicTypes
import DataCon
import TyCon
import TysWiredIn

import Data.Monoid
import Control.Applicative

-----------------------------------------------------------------------
-- | LH Primitive TyCons ----------------------------------------------
-----------------------------------------------------------------------

propTyCon, hpropTyCon :: TyCon 
propTyCon  = symbolTyCon 'w' 24 propConName
hpropTyCon = symbolTyCon 'w' 24 hpropConName  


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

wiredTyCons     = fst wiredTyDataCons
wiredDataCons   = snd wiredTyDataCons

wiredTyDataCons :: ([(TyCon, TyConP)] , [(DataCon, Located DataConP)])
wiredTyDataCons = (concat tcs, mapSnd dummyLoc <$> concat dcs)
  where 
    (tcs, dcs)  = unzip l
    l           = [listTyDataCons] ++ map tupleTyDataCons [2..maxArity]

listTyDataCons :: ([(TyCon, TyConP)] , [(DataCon, DataConP)])
listTyDataCons   = ( [(c, TyConP [(RTV tyv)] [p] [] [Covariant] [Covariant] (Just fsize))]
                   , [(nilDataCon, DataConP l0 [(RTV tyv)] [p] [] [] [] lt)
                   , (consDataCon, DataConP l0 [(RTV tyv)] [p] [] [] cargs  lt)])
    where
      l0         = dummyPos "LH.Bare.listTyDataCons"
      c          = listTyCon
      [tyv]      = tyConTyVarsDef c
      t          = rVar tyv :: RSort
      fld        = "fldList"
      x          = "xListSelector"
      xs         = "xsListSelector"
      p          = PV "p" (PVProp t) (vv Nothing) [(t, fld, EVar fld)]
      px         = pdVarReft $ PV "p" (PVProp t) (vv Nothing) [(t, fld, EVar x)] 
      lt         = rApp c [xt] [RPropP [] $ pdVarReft p] mempty                 
      xt         = rVar tyv
      xst        = rApp c [RVar (RTV tyv) px] [RPropP [] $ pdVarReft p] mempty
      cargs      = [(xs, xst), (x, xt)]
      fsize      = \x -> EApp (dummyLoc "len") [EVar x]

tupleTyDataCons :: Int -> ([(TyCon, TyConP)] , [(DataCon, DataConP)])
tupleTyDataCons n = ( [(c, TyConP (RTV <$> tyvs) ps [] tyvarinfo pdvarinfo Nothing)]
                    , [(dc, DataConP l0 (RTV <$> tyvs) ps [] []  cargs  lt)])
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
    ps            = mkps pnames (ta:ts) ((fld, EVar fld):(zip flds (EVar <$>flds)))
    ups           = uPVar <$> ps
    pxs           = mkps pnames (ta:ts) ((fld, EVar x1):(zip flds (EVar <$> xs)))
    lt            = rApp c (rVar <$> tyvs) (RPropP [] . pdVarReft <$> ups) mempty
    xts           = zipWith (\v p -> RVar (RTV v) (pdVarReft p)) tvs pxs
    cargs         = reverse $ (x1, rVar tv) : (zip xs xts)
    pnames        = mks_ "p"
    mks  x        = (\i -> symbol (x++ show i)) <$> [1..n]
    mks_ x        = (\i -> symbol (x++ show i)) <$> [2..n]


pdVarReft = (\p -> U mempty p mempty) . pdVar 

mkps ns (t:ts) ((f,x):fxs) = reverse $ mkps_ ns ts fxs [(t, f, x)] []
mkps _  _      _           = error "Bare : mkps"

mkps_ []     _       _          _    ps = ps
mkps_ (n:ns) (t:ts) ((f, x):xs) args ps = mkps_ ns ts xs (a:args) (p:ps)
  where
    p                                   = PV n (PVProp t) (vv Nothing) args
    a                                   = (t, f, x)
mkps_ _     _       _          _    _ = error "Bare : mkps_"

