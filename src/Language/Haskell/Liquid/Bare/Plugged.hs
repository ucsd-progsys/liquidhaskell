{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Language.Haskell.Liquid.Bare.Plugged 
  (  makePluggedSig
  , makePluggedAsmSigs
  , makePluggedDataCons
  ) where

import Prelude hiding (error)
import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)

import           Text.PrettyPrint.HughesPJ
import qualified Control.Exception                 as Ex
import qualified Data.HashMap.Strict               as M
import qualified Data.Maybe                        as Mb 
import qualified Language.Fixpoint.Types           as F
-- import qualified Language.Fixpoint.Types.Visitor   as F
import qualified Language.Haskell.Liquid.GHC.Misc  as GM 
import qualified Language.Haskell.Liquid.GHC.API   as Ghc 
import           Language.Haskell.Liquid.Types.RefType (updateRTVar, addTyConInfo, ofType, rVar, rTyVar, subts, toType, uReft)
import           Language.Haskell.Liquid.Types

import qualified Language.Haskell.Liquid.Misc       as Misc 
import qualified Language.Haskell.Liquid.Bare.Types as Bare
import qualified Language.Haskell.Liquid.Bare.Misc  as Bare
-- import Language.Haskell.Liquid.Bare.Env

--------------------------------------------------------------------------------
-- | NOTE: Be *very* careful with the use functions from RType -> GHC.Type,
--   e.g. toType, in this module as they cannot handle LH type holes. Since
--   this module is responsible for plugging the holes we obviously cannot
--   assume, as in e.g. L.H.L.Constraint.* that they do not appear.
--------------------------------------------------------------------------------
makePluggedSig :: ModName -> F.TCEmb Ghc.TyCon -> M.HashMap Ghc.TyCon RTyCon -> Ghc.NameSet
               -> Ghc.Var -> LocSpecType
               -> LocSpecType

makePluggedSig name embs tyi exports x t = 
    plugHoles embs tyi x r τ t
  where 
    τ = Ghc.expandTypeSynonyms (Ghc.varType x)
    r = maybeTrue x name exports

makePluggedAsmSigs :: F.TCEmb Ghc.TyCon
                   -> M.HashMap Ghc.TyCon RTyCon
                   -> [(Ghc.Var, LocSpecType)]
                   -> [(Ghc.Var, LocSpecType)]
makePluggedAsmSigs embs tyi sigs
  = [ (x, plugHoles embs tyi x r τ t) 
      | (x, t) <- sigs 
      , let τ = Ghc.expandTypeSynonyms (Ghc.varType x)
      , let r = const killHoles 
    ] 

for :: [a] -> (a -> b) -> [b]
for xs f = map f xs

makePluggedDataCons :: F.TCEmb Ghc.TyCon
                    -> M.HashMap Ghc.TyCon RTyCon
                    -> [Located DataConP]
                    -> [Located DataConP]
makePluggedDataCons embs tyi dcs
  = for dcs $ \ldcp -> 
       let dcp               = val            ldcp 
           dc                = dcpCon         dcp
           rest              = dcpTyRes       dcp
           (das, _, dts, dt) = Ghc.dataConSig dc
       in   if mismatch dts dcp 
             then (Ex.throw $ err dc dcp)
             else 
               let plug t1 t2 = plugHoles embs tyi (Ghc.dataConName dc) (const killHoles) t1 (F.atLoc ldcp t2)
                   tArgs      = zipWith (\t1 (x, t2) -> (x, val (plug t1 t2))) dts (reverse $ dcpTyArgs dcp)
                   tRes       = plugHoles embs tyi (Ghc.dataConName dc) (const killHoles) dt (F.atLoc ldcp rest)
               in
                  (F.atLoc ldcp $ dcp 
                    { dcpFreeTyVars = rTyVar <$> das
                    , dcpFreePred   = (subts (zip (dcpFreeTyVars dcp) ((rVar :: Ghc.TyVar -> RSort) <$> das))) <$> (dcpFreePred dcp)
                    , dcpTyArgs     = reverse tArgs
                    , dcpTyRes      = val tRes})

    where
      mismatch dts dcp = length dts /= length (dcpTyArgs dcp)
      err dc dcp       = ErrBadData (GM.fSrcSpan dcp) (pprint dc) "GHC and Liquid specifications have different numbers of fields" :: UserError

plugHoles, plugHoles_old, plugHoles_new 
  :: (Ghc.NamedThing a, PPrint a, Show a)
          => F.TCEmb Ghc.TyCon
          -> Bare.TyConMap 
          -> a
          -> (SpecType -> RReft -> RReft)
          -> Ghc.Type
          -> LocSpecType
          -> LocSpecType
plugHoles = plugHoles_old 

{- -}

-- NOTE: this use of toType is safe as rt' is derived from t.
plugHoles_old tce tyi x f t0 zz@(Loc l l' st0) 
    = Loc l l' 
    . mkArrow (updateRTVar <$> αs) ps (ls1 ++ ls2) [] [] 
    . makeCls cs' 
    . goPlug tce tyi f (subts su rt) 
    -- . mapExprReft (\_ -> F.applyCoSub coSub) 
    -- . subts su 
    $ st 
  where 
    tyvsmap           = case Bare.runMapTyVars (toType rt) st err of
                          Left e  -> Ex.throw e 
                          Right s -> Bare.vmap s
      
    su                = [(rTyVar x, y)           | (x, y) <- tyvsmap]
    -- su                = [(y, rTyVar x)           | (x, y) <- tyvsmap]
    su'               = [(y, RVar (rTyVar x) ()) | (x, y) <- tyvsmap] :: [(RTyVar, RSort)]
    -- coSub             = M.fromList [(F.symbol y, F.FObj (F.symbol x)) | (y, x) <- su]
    -- ps'               = fmap (subts su') <$> ps
    cs'               = [(F.dummySymbol, RApp c ts' [] mempty) 
                          | (c, ts) <- cs
                          , let ts' = subts su <$> ts
                        ]
    -- αs'               = undefined -- subts su <$> αs
    (αs,_,ls1,cs,rt)  = bkUnivClass (ofType (Ghc.expandTypeSynonyms t0) :: SpecType)
    (_,ps,ls2,_,st)   = bkUnivClass st0

    makeCls cs t      = foldr (uncurry rFun) t cs
    err               = ErrMismatch (GM.fSrcSpan zz) (pprint x) 
                          (text "Plugged Init types" {- <+> pprint t <+> "\nVS\n" <+> pprint st -})
                          (pprint $ Ghc.expandTypeSynonyms t0)
                          (pprint $ toRSort st0)
                          (Ghc.getSrcSpan x) 


plugHoles_new tce tyi x f t0 zz@(Loc l l' st0) 
    = Loc l l' 
    . mkArrow (updateRTVar <$> as') ps (ls1 ++ ls2) [] [] 
    . makeCls cs' 
    . goPlug tce tyi f rt' 
    -- . mapExprReft (\_ -> F.applyCoSub coSub) 
    -- . subts su 
    $ st 
  where 
    rt'               = tx rt
    as'               = subRTVar su <$> as
    cs'               = [ (F.dummySymbol, ct) | (c, t) <- cs, let ct = tx (RApp c t [] mempty) ]
    tx                = subts su
    su                = case Bare.runMapTyVars (toType rt) st err of
                          Left e  -> Ex.throw e 
                          Right s -> [ (rTyVar x, y) | (x, y) <- Bare.vmap s]
    (as,_,ls1,cs,rt)  = bkUnivClass (ofType (Ghc.expandTypeSynonyms t0) :: SpecType)
    (_,ps,ls2,_ ,st)  = bkUnivClass st0

    makeCls cs t      = foldr (uncurry rFun) t cs
    err               = ErrMismatch (GM.fSrcSpan zz) (pprint x) 
                          (text "Plugged Init types" {- <+> pprint t <+> "\nVS\n" <+> pprint st -})
                          (pprint $ Ghc.expandTypeSynonyms t0)
                          (pprint $ toRSort st0)
                          (Ghc.getSrcSpan x) 

subRTVar :: [(RTyVar, RTyVar)] -> SpecRTVar -> SpecRTVar 
subRTVar su a@(RTVar v i) = Mb.maybe a (`RTVar` i) (lookup v su)



bkUnivClass :: SpecType -> ([SpecRTVar],[PVar RSort], [F.Symbol], [(RTyCon, [SpecType])], SpecType )
bkUnivClass t        = (as, ps, ls, cs, t2) 
  where 
    (as, ps, ls, t1) = bkUniv  t
    (cs, t2)         = bkClass t1

goPlug :: F.TCEmb Ghc.TyCon -> Bare.TyConMap -> (SpecType -> RReft -> RReft) -> SpecType -> SpecType
       -> SpecType
goPlug tce tyi f = go 
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
    go (RAllT _ t)      (RAllT a t')       = RAllT a    (go t t')
    go (RAllT a t)      t'                 = RAllT a    (go t t')
    go t                (RAllP p t')       = RAllP p    (go t t')
    go t                (RAllS s t')       = RAllS s    (go t t')
    go t                (RAllE b a t')     = RAllE b a  (go t t')
    go t                (REx b x t')       = REx b x    (go t t')
    go t                (RRTy e r o t')    = RRTy e r o (go t t')
    go (RAppTy t1 t2 _) (RAppTy t1' t2' r) = RAppTy     (go t1 t1') (go t2 t2') r
    -- zipWithDefM: if ts and ts' have different length then the liquid and haskell types are different.
    -- keep different types for now, as a pretty error message will be created at Bare.Check
    go (RApp _ ts _ _)  (RApp c ts' p r)   --  length ts == length ts'
                                           = RApp c     (Misc.zipWithDef go ts $ Bare.matchKindArgs ts ts') p r
    -- If we reach the default case, there's probably an error, but we defer
    -- throwing it as checkGhcSpec does a much better job of reporting the
    -- problem to the user.
    go st               _                 = st

addRefs :: F.TCEmb Ghc.TyCon -> M.HashMap Ghc.TyCon RTyCon -> SpecType -> SpecType
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
