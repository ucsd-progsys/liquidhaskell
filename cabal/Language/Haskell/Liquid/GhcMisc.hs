{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}

module Language.Haskell.Liquid.GhcMisc where

import           Control.Applicative          ((<$>))
import           CoreSyn
import           CostCentre
import           FamInstEnv                   (FamInst)
import           GHC
import           HscTypes                     (Dependencies, ImportedMods, ModGuts(..))
import           Language.Haskell.Liquid.Misc (errorstar, stripParens)
import           Name                         (mkInternalName)
import           OccName                      (mkTyVarOcc)
import           Outputable
import           RdrName                      (GlobalRdrEnv)
import           Type                         (liftedTypeKind)
import           Unique                       (initTyVarUnique)
import           Var

-----------------------------------------------------------------------
--------------- Datatype For Holding GHC ModGuts ----------------------
-----------------------------------------------------------------------

data MGIModGuts = MI {
    mgi_binds     :: !CoreProgram
  , mgi_module    :: !Module
  , mgi_deps      :: !Dependencies
  , mgi_dir_imps  :: !ImportedMods
  , mgi_rdr_env   :: !GlobalRdrEnv
  , mgi_tcs       :: ![TyCon]
  , mgi_fam_insts :: ![FamInst]
  }

miModGuts mg = MI {
    mgi_binds     = mg_binds mg
  , mgi_module    = mg_module mg
  , mgi_deps      = mg_deps mg
  , mgi_dir_imps  = mg_dir_imps mg
  , mgi_rdr_env   = mg_rdr_env mg
  , mgi_tcs       = mg_tcs mg
  , mgi_fam_insts = mg_fam_insts mg
  }

-----------------------------------------------------------------------
--------------- Generic Helpers for Encoding Location -----------------
-----------------------------------------------------------------------

srcSpanTick :: Module -> SrcSpan -> Tickish a
srcSpanTick m loc
  = ProfNote (AllCafsCC m loc) False True

tickSrcSpan ::  Outputable a => Tickish a -> SrcSpan
tickSrcSpan (ProfNote (AllCafsCC _ loc) _ _)
  = loc
tickSrcSpan z
  = errorstar $ "tickSrcSpan: unhandled tick" ++ showPpr z

-----------------------------------------------------------------------
--------------- Generic Helpers for Accessing GHC Innards -------------
-----------------------------------------------------------------------

stringTyVar :: String -> TyVar
stringTyVar s = mkTyVar name liftedTypeKind
  where name = mkInternalName initTyVarUnique occ noSrcSpan
        occ  = mkTyVarOcc s

tvId α = {- traceShow ("tvId: α = " ++ show α) $ -} show α ++ show (varUnique α)

intersperse d ds = hsep $ punctuate (space <> d) ds

tracePpr s x = trace ("\nTrace: [" ++ s ++ "] : " ++ showPpr x) x

pprShow = text . show

dropModuleNames [] = []
dropModuleNames s  = last $ words $ dotWhite <$> stripParens s
  where dotWhite '.' = ' '
        dotWhite c   = c

--dropModuleNames x =  x -- (mylast x (words (dotWhite <$> x)))
--  where dotWhite '.' = ' '
--        dotWhite c   = c
--
--mylast x [] = error $ "RefType.last" ++ showPpr x
--mylast x l  = last l


--instance Outputable a => Outputable (S.Set a) where
--  ppr = ppr . S.toList
--
--instance (Outputable k, Outputable v) => Outputable (M.Map k v) where
--  ppr = ppr . M.toList

