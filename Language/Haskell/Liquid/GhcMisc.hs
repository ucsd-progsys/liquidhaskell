{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}

module Language.Haskell.Liquid.GhcMisc where

import           CoreSyn
import           CostCentre
import           FamInstEnv                   (FamInst)
import           GHC                          hiding (L)
import           HscTypes                     (Dependencies, ImportedMods, ModGuts(..))
import           Language.Haskell.Liquid.Misc (errorstar, stripParens)
import           Name                         (mkInternalName)
import           OccName                      (mkTyVarOcc)
import           Unique                       
import           Outputable
import           RdrName                      (GlobalRdrEnv)
import           Type                         (liftedTypeKind)
import           Var
import           FastString                   (uniq)
import           SrcLoc                       hiding (L)
import           Data.Char                    (isLower, isSpace)
import           Data.Hashable
import qualified Data.HashSet                 as S    
import           Control.Applicative          ((<$>))
import           Control.Exception            (assert)

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
        occ  = mkTyVarOcc $ assert (validTyVar s) s

validTyVar :: String -> Bool
validTyVar s@(c:_) = isLower c && all (not . isSpace) s 
validTyVar _       = False

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

-----------------------------------------------------------------------
------------------ Generic Helpers for DataConstructors ---------------
-----------------------------------------------------------------------

getDataConVarUnique v
  | isId v && isDataConWorkId v = getUnique $ idDataCon v
  | otherwise                   = getUnique v
  

newtype Loc    = L (Int, Int) deriving (Eq, Ord, Show)

instance Hashable Loc where
  hash (L z) = hash z 

--instance (Uniquable a) => Hashable a where
instance Hashable Var where
  hash = uniqueHash 

instance Hashable TyCon where
  hash = uniqueHash 

instance Hashable SrcSpan where
  hash (UnhelpfulSpan s) = hash (uniq s) 
  hash (RealSrcSpan s)   = hash (srcSpanStartLine s, srcSpanStartCol s, srcSpanEndCol s)

uniqueHash = hash . getKey . getUnique

instance Outputable a => Outputable (S.HashSet a) where
  ppr = ppr . S.toList 




