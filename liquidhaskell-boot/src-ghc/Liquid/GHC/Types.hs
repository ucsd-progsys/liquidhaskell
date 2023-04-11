{-# LANGUAGE DeriveGeneric #-}
module Liquid.GHC.Types where

import           Data.HashSet (HashSet, fromList)
import           Data.Hashable
import           GHC.Generics hiding (moduleName)
import           Liquid.GHC.API

-- | A 'StableName' is virtually isomorphic to a GHC's 'Name' but crucially we don't use
-- the 'Eq' instance defined on a 'Name' because it's 'Unique'-based. In particular, GHC
-- doesn't guarantee that if we load an interface multiple times we would get the same 'Unique' for the
-- same 'Name', and this is a problem when we rely on 'Name's to be the same when we call 'isExportedVar',
-- which used to use a 'NameSet' derived from the '[AvailInfo]'. As the name implies, a 'NameSet' uses a
-- 'Name's 'Unique' for duplicate detection and indexing, and this would lead to 'Var's being resolved to
-- a 'Name' which is basically the same, but it has a /different/ 'Unique', and that would cause the lookup
-- inside the 'NameSet' to fail.
newtype StableName =
  MkStableName { unStableName :: Name }
  deriving Generic

instance Show StableName where
  show (MkStableName n) = nameStableString n

instance Hashable StableName where
  hashWithSalt s (MkStableName n) = hashWithSalt s (nameStableString n)

instance Eq StableName where
  (MkStableName n1) == (MkStableName n2) = -- n1 `stableNameCmp` n2 == EQ
    let sameOccName = occNameString (nameOccName n1) == occNameString (nameOccName n2)
        sameModule  = nameModule  n1 == nameModule  n2
        sameSrcLoc  = nameSrcLoc  n1 == nameSrcLoc  n2
        sameSrcSpan = nameSrcSpan n1 == nameSrcSpan n2
    in sameOccName && sameModule && sameSrcLoc  && sameSrcSpan

-- | Creates a new 'StableName' out of a 'Name'.
mkStableName :: Name -> StableName
mkStableName = MkStableName

-- | Converts a list of 'AvailInfo' into a \"StableNameSet\", similarly to what 'availsToNameSet' would do.
availsToStableNameSet :: [AvailInfo] -> HashSet StableName
availsToStableNameSet avails = foldr add mempty avails
      where add av acc = acc <> fromList (map mkStableName (availNames av))

--------------------------------------------------------------------------------
-- | Datatype For Holding GHC ModGuts ------------------------------------------
--------------------------------------------------------------------------------
data MGIModGuts = MI
  { mgi_binds     :: !CoreProgram
  , mgi_module    :: !Module
  , mgi_deps      :: !Dependencies
  , mgi_dir_imps  :: ![ModuleName]
  , mgi_rdr_env   :: !GlobalRdrEnv
  , mgi_tcs       :: ![TyCon]
  , mgi_fam_insts :: ![FamInst]
  , mgi_exports   :: !(HashSet StableName)
  , mgi_cls_inst  :: !(Maybe [ClsInst])
  }

miModGuts :: Maybe [ClsInst] -> ModGuts -> MGIModGuts
miModGuts cls mg  = MI
  { mgi_binds     = mg_binds mg
  , mgi_module    = mg_module mg
  , mgi_deps      = mg_deps mg
  , mgi_dir_imps  = mgDirImps mg
  , mgi_rdr_env   = mg_rdr_env mg
  , mgi_tcs       = mg_tcs mg
  , mgi_fam_insts = mg_fam_insts mg
  , mgi_exports   = availsToStableNameSet $ mg_exports mg
  , mgi_cls_inst  = cls
  }

nameSetToStableNameSet :: NameSet -> HashSet StableName
nameSetToStableNameSet = fromList . map mkStableName . nameSetElemsStable

mgDirImps :: ModGuts -> [ModuleName]
mgDirImps = map gwib_mod . getDependenciesModuleNames . mg_deps

mgiNamestring :: MGIModGuts -> String
mgiNamestring = moduleNameString . moduleName . mgi_module
