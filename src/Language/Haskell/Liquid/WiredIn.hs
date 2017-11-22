{-# LANGUAGE OverloadedStrings #-}

module Language.Haskell.Liquid.WiredIn
       ( wiredTyCons
       , wiredDataCons
       , wiredSortedSyms

       -- | Constants for automatic proofs
       , dictionaryVar, dictionaryTyVar, dictionaryBind
       , proofTyConName, combineProofsName

       -- | Built  in Symbols
       , isWiredIn
       , dcPrefix

       ) where

import Prelude                                hiding (error)
import Var

import Language.Haskell.Liquid.Types
import Language.Fixpoint.Misc           (mapSnd)
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.Types.Variance
import Language.Haskell.Liquid.Types.PredType
import Language.Fixpoint.Types hiding (panic)
import qualified Language.Fixpoint.Types as F

import BasicTypes
import DataCon
import TyCon
import TysWiredIn

import Language.Haskell.Liquid.GHC.TypeRep
import CoreSyn hiding (mkTyArg)

-- | Horrible hack to support hardwired symbols like
--      `head`, `tail`, `fst`, `snd`
--   and other LH generated symbols that
--   *do not* correspond to GHC Vars and
--   *should not* be resolved to GHC Vars.

isWiredIn :: Located Symbol -> Bool
isWiredIn x = isWiredInLoc x  || isWiredInName x || isWiredInShape x

isWiredInLoc :: Located Symbol -> Bool
isWiredInLoc x  = l == l' && l == 0 && c == c' && c' == 0
  where
    (l , c)  = spe (loc x)
    (l', c') = spe (locE x)
    spe l    = (x, y) where (_, x, y) = sourcePosElts l

isWiredInName :: Located Symbol -> Bool
isWiredInName x = (val x) `elem` wiredInNames

wiredInNames :: [F.Symbol]
wiredInNames = [ "head", "tail", "fst", "snd", "len" ]

isWiredInShape :: Located Symbol -> Bool
isWiredInShape x = any (`F.isPrefixOfSym` (val x)) [F.anfPrefix, F.tempPrefix, dcPrefix]
  -- where s        = val x
        -- dcPrefix = "lqdc"

dcPrefix :: F.Symbol
dcPrefix = "lqdc"

wiredSortedSyms :: [(Symbol, Sort)]
wiredSortedSyms = [(pappSym n, pappSort n) | n <- [1..pappArity]]

--------------------------------------------------------------------------------
-- | LH Primitive TyCons -------------------------------------------------------
--------------------------------------------------------------------------------

dictionaryVar :: Var
dictionaryVar   = stringVar "tmp_dictionary_var" (ForAllTy (TvBndr dictionaryTyVar Required) $ TyVarTy dictionaryTyVar)

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

--------------------------------------------------------------------------------
-- | Predicate Types for WiredIns ----------------------------------------------
--------------------------------------------------------------------------------

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
listTyDataCons   = ( [(c, TyConP l0 [RTV tyv] [p] [] [Covariant] [Covariant] (Just fsize))]
                   , [(nilDataCon , DataConP l0 [RTV tyv] [p] [] [] []    lt False wiredInName l0)
                     ,(consDataCon, DataConP l0 [RTV tyv] [p] [] [] cargs lt False wiredInName l0)])
    where
      l0         = dummyPos "LH.Bare.listTyDataCons"
      c          = listTyCon
      [tyv]      = tyConTyVarsDef c
      t          = rVar tyv :: RSort
      fld        = "fldList"
      xHead      = "head"
      xTail      = "tail"
      p          = PV "p" (PVProp t) (vv Nothing) [(t, fld, EVar fld)]
      px         = pdVarReft $ PV "p" (PVProp t) (vv Nothing) [(t, fld, EVar xHead)]
      lt         = rApp c [xt] [rPropP [] $ pdVarReft p] mempty
      xt         = rVar tyv
      xst        = rApp c [RVar (RTV tyv) px] [rPropP [] $ pdVarReft p] mempty
      cargs      = [(xTail, xst), (xHead, xt)]
      fsize      = SymSizeFun (dummyLoc "len")

wiredInName :: Symbol
wiredInName = "WiredIn"

tupleTyDataCons :: Int -> ([(TyCon, TyConP)] , [(DataCon, DataConP)])
tupleTyDataCons n = ( [(c, TyConP l0 (RTV <$> tyvs) ps [] tyvarinfo pdvarinfo Nothing)]
                    , [(dc, DataConP l0 (RTV <$> tyvs) ps [] []  cargs  lt False wiredInName l0)])
  where
    tyvarinfo     = replicate n     Covariant
    pdvarinfo     = replicate (n-1) Covariant
    l0            = dummyPos "LH.Bare.tupleTyDataCons"
    c             = tupleTyCon   Boxed n
    dc            = tupleDataCon Boxed n
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
