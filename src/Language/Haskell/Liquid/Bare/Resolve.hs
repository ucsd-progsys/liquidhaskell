-- | This module has the code that uses the GHC definitions to:
--   1. MAKE a name-resolution environment,
--   2. USE the environment to translate plain symbols into Var, TyCon, etc. 

module Language.Haskell.Liquid.Bare.Resolve 
  ( -- * Name resolution Environment 
    Env 
    
    -- * Creating the Environment
  , makeEnv 

    -- * Using the Environment 
  , ResolveSym (..)
  , strictResolveSym 
  , Resolvable (..)
  ) where 

import qualified Var                             as Ghc
import qualified Module                          as Ghc
import qualified GHC                             as Ghc
import qualified Language.Fixpoint.Types         as F 
import qualified Language.Haskell.Liquid.Types   as Types 
import qualified Language.Haskell.Liquid.Measure as Ms

-------------------------------------------------------------------------------
-- | Name resolution environment (DO NOT EXPORT!) 
-------------------------------------------------------------------------------
data Env = RE 
  { reLMap :: !Types.LogicMap
  }

--  { reMod  :: Types.ModName     -- ^ Name of (target)
--  , reVars :: 
--  } 

-------------------------------------------------------------------------------
-- | Creating an environment 
-------------------------------------------------------------------------------
makeEnv :: Types.GhcSrc -> [(Types.ModName, Ms.BareSpec)] -> Types.LogicMap -> Env 
makeEnv _src _specs lmap = RE 
  { reLMap = lmap
  } 

-------------------------------------------------------------------------------
-- | Using the environment 
-------------------------------------------------------------------------------
class ResolveSym a where 
  resolveSym :: Env -> Types.ModName -> String -> Types.LocSymbol -> Either Types.UserError a 

instance ResolveSym Ghc.Var where 
  resolveSym = error "TBD:resolve (Var)"

instance ResolveSym Ghc.TyCon where 
  resolveSym = error "TBD:resolve (TyCon)"

-- | @strictResolve@ wraps the plain @resolve@ to throw an error 
--   if the name being searched for is unknown.
strictResolveSym :: (ResolveSym a) => Env -> Types.ModName -> String -> Types.LocSymbol -> a 
strictResolveSym env name x kind = case resolveSym env name x kind of 
  Left  err -> Types.uError err 
  Right val -> val 

class Resolvable a where 
  resolve :: Env -> Types.ModName -> F.SourcePos -> a -> a  

instance Resolvable F.Qualifier where 
  resolve = undefined 