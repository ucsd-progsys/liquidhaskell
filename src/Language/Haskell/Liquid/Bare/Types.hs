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
  , TyConMap

    -- * Signature processing environment 
  , SigEnv (..)

    -- * Measure related environment 
  , MeasEnv (..)
  ) where 

import qualified Data.HashMap.Strict             as M
import qualified Language.Fixpoint.Types         as F 
import qualified Language.Haskell.Liquid.Measure as Ms
import           Language.Haskell.Liquid.Types.Types   
import           Language.Haskell.Liquid.Types.Specs 
import           Language.Haskell.Liquid.GHC.API as Ghc hiding (Located) 


type ModSpecs = M.HashMap ModName Ms.BareSpec

-------------------------------------------------------------------------------
-- | Name resolution environment 
-------------------------------------------------------------------------------
data Env = RE 
  { reLMap      :: !LogicMap
  , reSyms      :: ![(F.Symbol, Ghc.Var)]    -- ^ see "syms" in old makeGhcSpec'
  -- , _reSpecs     :: !ModSpecs 
  , _reSubst    :: !F.Subst                  -- ^ see "su"   in old makeGhcSpec'
  , _reTyThings :: !TyThingMap 
  , reCfg       :: !Config
  , reQImps     :: !QImports                 -- ^ qualified imports
  , reLocalVars :: !LocalVars                -- ^ lines at which local variables are defined.
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
  , sigTyRTyMap   :: !(M.HashMap Ghc.TyCon RTyCon)
  , sigExports    :: !Ghc.NameSet
  , sigRTEnv      :: !BareRTEnv
  }

-------------------------------------------------------------------------------
-- | A @TycEnv@ contains the information needed to process Type- and Data- Constructors 
-------------------------------------------------------------------------------
data TycEnv = TycEnv 
  { tcTyCons      :: ![TyConP]
  , tcDataCons    :: ![DataConP]
  , tcSelMeasures :: ![Measure SpecType Ghc.DataCon]
  , tcSelVars     :: ![(Ghc.Var, Located SpecType)]
  , tcTyConMap    :: !TyConMap 
  , tcAdts        :: ![F.DataDecl]
  , tcDataConMap  :: !DataConMap 
  , tcEmbs        :: !(F.TCEmb Ghc.TyCon)
  , tcName        :: !ModName
  }

type TyConMap   = M.HashMap Ghc.TyCon RTyCon
type DataConMap = M.HashMap (F.Symbol, Int) F.Symbol

-------------------------------------------------------------------------------
-- | Intermediate representation for Measure information 
-------------------------------------------------------------------------------
-- REBARE: used to be output of makeGhcSpecCHOP2
data MeasEnv = MeasEnv 
  { meMeasureSpec :: !(MSpec SpecType Ghc.DataCon)          -- measures
  , meClassSyms   :: ![(F.Symbol, Located (RRType F.Reft))] -- cms' 
  , meSyms        :: ![(F.Symbol, Located (RRType F.Reft))] -- ms' 
  , meDataCons    :: ![(Ghc.Var,  LocSpecType)]             -- cs'
                                                            -- xs' :: [Symbol] = fst <$> meSyms
  }

{- 
data BareEnv = BE
  { modName  :: !ModName
  , tcEnv    :: !TCEnv
  , rtEnv    :: !RTEnv
  , varEnv   :: !(M.HashMap F.Symbol Var)
  , hscEnv   :: !(HscEnv)
  , famEnv   :: !(M.HashMap F.Symbol DataCon)     -- ^ see NOTE:Family-Instance-Environment
  , logicEnv :: !LogicMap
  , dcEnv    :: !DataConMap
  , bounds   :: !(RBEnv)
  , embeds   :: !(TCEmb TyCon)
  , axSyms   :: !(M.HashMap F.Symbol LocSymbol)
  , propSyms :: !(M.HashMap F.Symbol LocSymbol)
  , beConfig :: !Config
  , beIndex  :: !Integer
  }
-}