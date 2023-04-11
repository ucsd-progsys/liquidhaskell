-- | This module has the code that uses the GHC definitions to:
--   1. MAKE a name-resolution environment,
--   2. USE the environment to translate plain symbols into Var, TyCon, etc. 

module Language.Haskell.Liquid.Bare.Types 
  ( -- * Name resolution environment 
    Env (..)
  , TyThingMap 
  , ModSpecs
  , LocalVars 

    -- * Tycon and Datacon processing environment
  , TycEnv (..) 
  , DataConMap
  , RT.TyConMap

    -- * Signature processing environment 
  , SigEnv (..)

    -- * Measure related environment 
  , MeasEnv (..)

    -- * Misc 
  , PlugTV (..)
  , plugSrc
  , varRSort 
  , varSortedReft
  , failMaybe
  ) where 

import qualified Text.PrettyPrint.HughesPJ             as PJ 
import qualified Data.HashSet                          as S
import qualified Data.HashMap.Strict                   as M
import qualified Language.Fixpoint.Types               as F 
import qualified Language.Haskell.Liquid.Measure       as Ms
import qualified Language.Haskell.Liquid.Types.RefType as RT 
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Specs   hiding (BareSpec)
import           Liquid.GHC.API       as Ghc hiding (Located, Env)
import           Liquid.GHC.Types     (StableName)


type ModSpecs = M.HashMap ModName Ms.BareSpec

-------------------------------------------------------------------------------
-- | See [NOTE: Plug-Holes-TyVars] for a rationale for @PlugTV@ 
-------------------------------------------------------------------------------

data PlugTV v 
  = HsTV v  -- ^ Use tyvars from GHC specification (in the `v`) 
  | LqTV v  -- ^ Use tyvars from Liquid specification
  | GenTV   -- ^ Generalize ty-vars 
  | RawTV   -- ^ Do NOT generalize ty-vars (e.g. for type-aliases)
  deriving (Show)


instance (Show v, F.PPrint v) => F.PPrint (PlugTV v) where 
  pprintTidy _ = PJ.text . show 
   
plugSrc ::  PlugTV v -> Maybe v 
plugSrc (HsTV v) = Just v 
plugSrc (LqTV v) = Just v 
plugSrc _        = Nothing

-------------------------------------------------------------------------------
-- | Name resolution environment 
-------------------------------------------------------------------------------
data Env = RE 
  { reLMap      :: !LogicMap
  , reSyms      :: ![(F.Symbol, Ghc.Var)]    -- ^ see "syms" in old makeGhcSpec'
  , _reSubst    :: !F.Subst                  -- ^ see "su"   in old makeGhcSpec'
  , _reTyThings :: !TyThingMap 
  , reCfg       :: !Config
  , reQualImps  :: !QImports                 -- ^ qualified imports
  , reAllImps   :: !(S.HashSet F.Symbol)     -- ^ all imported modules
  , reLocalVars :: !LocalVars                -- ^ lines at which local variables are defined.
  , reGlobSyms  :: !(S.HashSet F.Symbol)     -- ^ global symbols, typically unlifted measures like 'len', 'fromJust'
  , reSrc       :: !GhcSrc                   -- ^ all source info
  }

instance HasConfig Env where 
  getConfig = reCfg 

-- | @LocalVars@ is a map from names to lists of pairs of @Ghc.Var@ and 
--   the lines at which they were defined. 
type LocalVars = M.HashMap F.Symbol [(Int, Ghc.Var)]

-------------------------------------------------------------------------------
-- | A @TyThingMap@ is used to resolve symbols into GHC @TyThing@ and, 
--   from there into Var, TyCon, DataCon, etc.
-------------------------------------------------------------------------------
type TyThingMap = M.HashMap F.Symbol [(F.Symbol, Ghc.TyThing)]

-------------------------------------------------------------------------------
-- | A @SigEnv@ contains the needed to process type signatures 
-------------------------------------------------------------------------------
data SigEnv = SigEnv 
  { sigEmbs       :: !(F.TCEmb Ghc.TyCon) 
  , sigTyRTyMap   :: !RT.TyConMap 
  , sigExports    :: !(S.HashSet StableName)
  , sigRTEnv      :: !BareRTEnv
  }

-------------------------------------------------------------------------------
-- | A @TycEnv@ contains the information needed to process Type- and Data- Constructors 
-------------------------------------------------------------------------------
data TycEnv = TycEnv 
  { tcTyCons      :: ![TyConP]
  , tcDataCons    :: ![DataConP]
  , tcSelMeasures :: ![Measure SpecType Ghc.DataCon]
  , tcSelVars     :: ![(Ghc.Var, LocSpecType)]
  , tcTyConMap    :: !RT.TyConMap 
  , tcAdts        :: ![F.DataDecl]
  , tcDataConMap  :: !DataConMap 
  , tcEmbs        :: !(F.TCEmb Ghc.TyCon)
  , tcName        :: !ModName
  }

type DataConMap = M.HashMap (F.Symbol, Int) F.Symbol

-------------------------------------------------------------------------------
-- | Intermediate representation for Measure information 
-------------------------------------------------------------------------------
-- REBARE: used to be output of makeGhcSpecCHOP2
data MeasEnv = MeasEnv 
  { meMeasureSpec :: !(MSpec SpecType Ghc.DataCon)          
  , meClassSyms   :: ![(F.Symbol, Located (RRType F.Reft))] 
  , meSyms        :: ![(F.Symbol, Located (RRType F.Reft))]
  , meDataCons    :: ![(Ghc.Var,  LocSpecType)]           
  , meClasses     :: ![DataConP]                           
  , meMethods     :: ![(ModName, Ghc.Var, LocSpecType)]  
  , meCLaws       :: ![(Ghc.Class, [(ModName, Ghc.Var, LocSpecType)])]  
  }

instance Semigroup MeasEnv where
  (<>) = error "FIXME:1773"
instance Monoid MeasEnv where
  mempty = error "FIXME:1773"

-------------------------------------------------------------------------------
-- | Converting @Var@ to @Sort@
-------------------------------------------------------------------------------
varSortedReft :: F.TCEmb Ghc.TyCon -> Ghc.Var -> F.SortedReft 
varSortedReft emb = RT.rTypeSortedReft emb . varRSort 

varRSort  :: Ghc.Var -> RSort
varRSort  = RT.ofType . Ghc.varType

-------------------------------------------------------------------------------
-- | Handling failed resolution 
-------------------------------------------------------------------------------
failMaybe :: Env -> ModName -> Either e r -> Either e (Maybe r)
failMaybe env name res = case res of 
  Right r -> Right (Just r) 
  Left  e -> if isTargetModName env name 
              then Left e
              else Right Nothing 

isTargetModName :: Env -> ModName -> Bool 
isTargetModName env name = name == _giTargetMod (reSrc env) 
