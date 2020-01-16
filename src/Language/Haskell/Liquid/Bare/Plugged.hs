{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Language.Haskell.Liquid.Bare.Plugged 
  ( makePluggedSig
  , makePluggedDataCon
  ) where

import Prelude hiding (error)
import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)

import           Text.PrettyPrint.HughesPJ
import qualified Control.Exception                 as Ex
import qualified Data.HashMap.Strict               as M
import qualified Data.Maybe                        as Mb 
import qualified Language.Fixpoint.Types           as F
import qualified Language.Fixpoint.Types.Visitor   as F
import qualified Language.Haskell.Liquid.GHC.Misc  as GM 
import qualified Language.Haskell.Liquid.GHC.API   as Ghc 
import           Language.Haskell.Liquid.Types.RefType (updateRTVar, addTyConInfo, ofType, rTyVar, subts, toType, uReft)
import           Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Misc       as Misc 
import qualified Language.Haskell.Liquid.Bare.Types as Bare
import qualified Language.Haskell.Liquid.Bare.Misc  as Bare

---------------------------------------------------------------------------------------
-- [NOTE: Plug-Holes-TyVars] We have _two_ versions of `plugHoles:
-- * `HsTyVars` ensures that the returned signature uses the GHC type variables;
--   We need this as these tyvars can appear in the SOURCE (as type annotations, or
--   as the types of lambdas) and renaming them will cause problems; 
-- * `LqTyVars` ensures that the returned signatuer uses the LIQUID type variables; 
--   We need this e.g. for class specifications where we cannot change the tyvars 
--   used inside method signatures as that messes up the type for the data-constructor 
--   for the dictionary (as we need to use the same tyvars as are "bound" in the class 
--   definition).
-- In short, use `HsTyVars` when we also have to analyze the binder's SOURCE; and 
-- otherwise, use `LqTyVars`.
---------------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- | NOTE: Be *very* careful with the use functions from RType -> GHC.Type,
--   e.g. toType, in this module as they cannot handle LH type holes. Since
--   this module is responsible for plugging the holes we obviously cannot
--   assume, as in e.g. L.H.L.Constraint.* that they do not appear.
--------------------------------------------------------------------------------
makePluggedSig :: ModName -> F.TCEmb Ghc.TyCon -> TyConMap -> Ghc.NameSet
               -> Bare.PlugTV Ghc.Var -> LocSpecType
               -> LocSpecType

makePluggedSig name embs tyi exports kx t 
  | Just x <- kxv = mkPlug x 
  | otherwise     = t
  where 
    kxv           = Bare.plugSrc kx
    mkPlug x      = plugHoles kx embs tyi  r τ t
      where
        τ         = Ghc.expandTypeSynonyms (Ghc.varType x)
        r         = maybeTrue x name exports
    -- x = case kx of { Bare.HsTV x -> x ; Bare.LqTV x -> x }


-- makePluggedDataCon = makePluggedDataCon_old 
-- plugHoles          = plugHoles_old 
-- makePluggedDataCon = makePluggedDataCon_new 

-- plugHoles _         = plugHoles_old

plugHoles :: (Ghc.NamedThing a, PPrint a, Show a) 
          => Bare.PlugTV a
          -> F.TCEmb Ghc.TyCon
          -> Bare.TyConMap
          -> (SpecType -> RReft -> RReft)
          -> Ghc.Type
          -> LocSpecType
          -> LocSpecType
plugHoles (Bare.HsTV x) a b = plugHoles_old a b x 
plugHoles (Bare.LqTV x) a b = plugHoles_new a b x 
plugHoles _             _ _ = \_ _ t -> t


makePluggedDataCon :: F.TCEmb Ghc.TyCon -> Bare.TyConMap -> Located DataConP -> Located DataConP
makePluggedDataCon embs tyi ldcp 
  | mismatchFlds      = Ex.throw (err "fields")
  | mismatchTyVars    = Ex.throw (err "type variables")
  | otherwise         = F.atLoc ldcp $ F.notracepp "makePluggedDataCon" $ dcp 
                          { dcpTyArgs     = reverse tArgs 
                          , dcpTyRes      = tRes 
                          }
  where 
    (tArgs, tRes)     = plugMany       embs tyi ldcp (das, dts, dt) (dcVars, dcArgs, dcpTyRes dcp)
    (das, _, dts, dt) = {- F.notracepp ("makePluggedDC: " ++ F.showpp dc) $ -} Ghc.dataConSig dc
    dcArgs            = reverse (dcpTyArgs dcp)
    dcVars            = dcpFreeTyVars dcp 
    dc                = dcpCon        dcp
    dcp               = val           ldcp 

    mismatchFlds      = length dts /= length dcArgs 
    mismatchTyVars    = length das /= length dcVars 
    err things        = ErrBadData (GM.fSrcSpan dcp) (pprint dc) ("GHC and Liquid specifications have different numbers of" <+> things) :: UserError



-- | @plugMany@ is used to "simultaneously" plug several different types, 
--   e.g. as arise in the fields of a data constructor. To do so we create 
--   a single "function type" that is then passed into @plugHoles@. 
--   We also pass in the type parameters as dummy arguments, because, e.g. 
--   we want @plugMany@ on the two types
--  
--      forall a. a -> a -> Bool 
--      forall b. _ -> _ -> _ 
-- 
--   to return something like 
-- 
--      forall b. b -> b -> Bool
-- 
--   and not, forall b. a -> a -> Bool.

plugMany :: F.TCEmb Ghc.TyCon -> Bare.TyConMap 
         -> Located DataConP            
         -> ([Ghc.Var], [Ghc.Type],             Ghc.Type)   -- ^ hs type 
         -> ([RTyVar] , [(F.Symbol, SpecType)], SpecType)   -- ^ lq type 
         -> ([(F.Symbol, SpecType)], SpecType)              -- ^ plugged lq type
plugMany embs tyi ldcp (hsAs, hsArgs, hsRes) (lqAs, lqArgs, lqRes) 
                     = F.notracepp msg (drop nTyVars (zip xs ts), t) 
  where 
    (_,(xs,ts,_), t) = bkArrow (val pT) 
    pT               = plugHoles (Bare.LqTV dcName) embs tyi (const killHoles) hsT (F.atLoc ldcp lqT)
    -- TODO(adinapoli) Is 'VisArg' what we really want here?
    hsT              = foldr (Ghc.mkFunTy Ghc.VisArg) hsRes hsArgs' 
    lqT              = foldr (uncurry rFun) lqRes lqArgs' 
    hsArgs'          = [ Ghc.mkTyVarTy a               | a <- hsAs] ++ hsArgs 
    lqArgs'          = [(F.dummySymbol, RVar a mempty) | a <- lqAs] ++ lqArgs 
    nTyVars          = length hsAs -- == length lqAs
    dcName           = Ghc.dataConName . dcpCon . val $ ldcp
    msg              = "plugMany: " ++ F.showpp (dcName, hsT, lqT)

plugHoles_old, plugHoles_new 
  :: (Ghc.NamedThing a, PPrint a, Show a)
  => F.TCEmb Ghc.TyCon
  -> Bare.TyConMap 
  -> a
  -> (SpecType -> RReft -> RReft)
  -> Ghc.Type
  -> LocSpecType
  -> LocSpecType
  
-- NOTE: this use of toType is safe as rt' is derived from t.
plugHoles_old tce tyi x f t0 zz@(Loc l l' st0) 
    = Loc l l' 
    . mkArrow (zip (updateRTVar <$> αs') rs) ps' [] [] 
    . makeCls cs' 
    . goPlug tce tyi err f (subts su rt) 
    . mapExprReft (\_ -> F.applyCoSub coSub) 
    . subts su 
    $ st 
  where 
    tyvsmap      = case Bare.runMapTyVars (toType rt) st err of
                          Left e  -> Ex.throw e 
                          Right s -> Bare.vmap s
    su           = [(y, rTyVar x)           | (x, y) <- tyvsmap]
    su'          = [(y, RVar (rTyVar x) ()) | (x, y) <- tyvsmap] :: [(RTyVar, RSort)]
    coSub        = M.fromList [(F.symbol y, F.FObj (F.symbol x)) | (y, x) <- su]
    ps'          = fmap (subts su') <$> ps
    cs'          = [(F.dummySymbol, RApp c ts [] mempty) | (c, ts) <- cs ] 
    (αs', rs)    = unzip αs
    (αs,_,cs,rt) = bkUnivClass (F.notracepp "hs-spec" $ ofType (Ghc.expandTypeSynonyms t0) :: SpecType)
    (_,ps,_ ,st) = bkUnivClass (F.notracepp "lq-spec" st0)

    makeCls cs t = foldr (uncurry rFun) t cs
    err hsT lqT  = ErrMismatch (GM.fSrcSpan zz) (pprint x) 
                          (text "Plugged Init types old")
                          (pprint $ Ghc.expandTypeSynonyms t0)
                          (pprint $ toRSort st0)
                          (Just (hsT, lqT))
                          (Ghc.getSrcSpan x) 


plugHoles_new tce tyi x f t0 zz@(Loc l l' st0) 
    = Loc l l' 
    . mkArrow (zip (updateRTVar <$> as'') rs) ps [] [] 
    . makeCls cs' 
    . goPlug tce tyi err f rt' 
    $ st 
  where 
    rt'          = tx rt
    as''         = subRTVar su <$> as'
    (as',rs)     = unzip as 
    cs'          = [ (F.dummySymbol, ct) | (c, t) <- cs, let ct = tx (RApp c t [] mempty) ]
    tx           = subts su
    su           = case Bare.runMapTyVars (toType rt) st err of
                          Left e  -> Ex.throw e 
                          Right s -> [ (rTyVar x, y) | (x, y) <- Bare.vmap s]
    (as,_,cs,rt) = bkUnivClass (ofType (Ghc.expandTypeSynonyms t0) :: SpecType)
    (_,ps,_ ,st) = bkUnivClass st0

    makeCls cs t = foldr (uncurry rFun) t cs
    err hsT lqT  = ErrMismatch (GM.fSrcSpan zz) (pprint x) 
                          (text "Plugged Init types new")
                          (pprint $ Ghc.expandTypeSynonyms t0)
                          (pprint $ toRSort st0)
                          (Just (hsT, lqT))
                          (Ghc.getSrcSpan x) 

subRTVar :: [(RTyVar, RTyVar)] -> SpecRTVar -> SpecRTVar 
subRTVar su a@(RTVar v i) = Mb.maybe a (`RTVar` i) (lookup v su)

goPlug :: F.TCEmb Ghc.TyCon -> Bare.TyConMap -> (Doc -> Doc -> Error) -> (SpecType -> RReft -> RReft) -> SpecType -> SpecType
       -> SpecType
goPlug tce tyi err f = go 
  where
    go t (RHole r) = (addHoles t') { rt_reft = f t r }
      where
        t'         = everywhere (mkT $ addRefs tce tyi) t
        addHoles   = everywhere (mkT $ addHole)
        -- NOTE: make sure we only add holes to RVar and RApp (NOT RFun)
        addHole :: SpecType -> SpecType
        addHole t@(RVar v _)       = RVar v (f t (uReft ("v", hole)))
        addHole t@(RApp c ts ps _) = RApp c ts ps (f t (uReft ("v", hole)))
        addHole t                  = t

    go (RVar _ _)       v@(RVar _ _)       = v
    go t'               (RImpF x i o r)    = RImpF x i  (go t' o)             r
    go (RFun _ i o _)   (RFun x i' o' r)   = RFun x     (go i i')   (go o o') r
    go (RAllT _ t _)    (RAllT a t' r)     = RAllT a    (go t t') r
    go (RAllT a t r)    t'                 = RAllT a    (go t t') r
    go t                (RAllP p t')       = RAllP p    (go t t')
    go t                (RAllE b a t')     = RAllE b a  (go t t')
    go t                (REx b x t')       = REx b x    (go t t')
    go t                (RRTy e r o t')    = RRTy e r o (go t t')
    go (RAppTy t1 t2 _) (RAppTy t1' t2' r) = RAppTy     (go t1 t1') (go t2 t2') r
    -- zipWithDefM: if ts and ts' have different length then the liquid and haskell types are different.
    -- keep different types for now, as a pretty error message will be created at Bare.Check
    go (RApp _ ts _ _)  (RApp c ts' p r)   
      | length ts == length ts'            = RApp c     (Misc.zipWithDef go ts $ Bare.matchKindArgs ts ts') p r
    go hsT lqT                             = Ex.throw (err (F.pprint hsT) (F.pprint lqT))

    -- otherwise                          = Ex.throw err 
    -- If we reach the default case, there's probably an error, but we defer
    -- throwing it as checkGhcSpec does a much better job of reporting the
    -- problem to the user.
    -- go st               _                 = st

addRefs :: F.TCEmb Ghc.TyCon -> TyConMap -> SpecType -> SpecType
addRefs tce tyi (RApp c ts _ r) = RApp c' ts ps r
  where
    RApp c' _ ps _ = addTyConInfo tce tyi (RApp c ts [] r)
addRefs _ _ t  = t

maybeTrue :: Ghc.NamedThing a => a -> ModName -> Ghc.NameSet -> SpecType -> RReft -> RReft
maybeTrue x target exports t r
  | not (isFunTy t) && (Ghc.isInternalName name || inTarget && notExported)
  = r
  | otherwise
  = killHoles r
  where
    inTarget    = Ghc.moduleName (Ghc.nameModule name) == getModName target
    name        = Ghc.getName x
    notExported = not (Ghc.getName x `Ghc.elemNameSet` exports)

-- killHoles r@(U (Reft (v, rs)) _ _) = r { ur_reft = Reft (v, filter (not . isHole) rs) }

killHoles :: RReft -> RReft
killHoles ur = ur { ur_reft = tx $ ur_reft ur }
  where
    tx r = {- traceFix ("killholes: r = " ++ showFix r) $ -} F.mapPredReft dropHoles r
    dropHoles    = F.pAnd . filter (not . isHole) . F.conjuncts
