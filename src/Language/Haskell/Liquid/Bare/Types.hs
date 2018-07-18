-- | This module has the code that uses the GHC definitions to:
--   1. MAKE a name-resolution environment,
--   2. USE the environment to translate plain symbols into Var, TyCon, etc. 

module Language.Haskell.Liquid.Bare.Types 
  ( -- * Name resolution environment 
    Env (..)

    -- * Tycon and Datacon environment
  , TycEnv (..) 

  , DataConMap

  ) where 

import qualified Data.HashMap.Strict             as M

import qualified Var                             as Ghc
import qualified Module                          as Ghc
import qualified GHC                             as Ghc

import qualified Language.Fixpoint.Types         as F 
import qualified Language.Haskell.Liquid.Measure as Ms
import           Language.Haskell.Liquid.Types   

-------------------------------------------------------------------------------
-- | Name resolution environment 
-------------------------------------------------------------------------------
data Env = RE 
  { reLMap  :: !LogicMap
  , reSyms  :: ![(F.Symbol, Ghc.Var)]           -- ^ see "syms" in old makeGhcSpec'
  , reSpecs :: ![(ModName, Ms.BareSpec)] 
  }

-------------------------------------------------------------------------------
-- | Type- and Data- Constructor Environment 
-------------------------------------------------------------------------------

data TycEnv = TycEnv 
  { tcTyCons      :: ![(Ghc.TyCon, TyConP)]
  , tcDataCons    :: ![(Ghc.DataCon, DataConP)]
  , tcSelMeasures :: ![Measure SpecType Ghc.DataCon]
  , tcSelVars     :: ![(Ghc.Var, Located SpecType)]
  , tcTyRTyMap    :: !(M.HashMap Ghc.TyCon RTyCon)
  , tcAdts        :: ![F.DataDecl]
  , tcDataConMap  :: !DataConMap 
  }

type DataConMap = M.HashMap (F.Symbol, Int) F.Symbol

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