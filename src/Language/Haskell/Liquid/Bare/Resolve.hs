-- | This module has the code that uses the GHC definitions to:
--   1. MAKE a name-resolution environment,
--   2. USE the environment to translate plain symbols into Var, TyCon, etc. 

module Language.Haskell.Liquid.Bare.Resolve 
  ( -- * Name resolution Environment 
    Env 
    
    -- * Creating the Environment
  , makeEnv 

    -- * Using the Environment 
  , Resolve (..)
  , strictResolve 
  ) where 

import qualified Var    as Ghc
import qualified Module as Ghc

import qualified Language.Haskell.Liquid.Types as Types 

-------------------------------------------------------------------------------
-- | Name resolution environment (DO NOT EXPORT!) 
-------------------------------------------------------------------------------
data Env = RE {}
--  { reMod  :: Types.ModName     -- ^ Name of (target)
--  , reVars :: 
--  } 

-------------------------------------------------------------------------------
-- | Creating an environment 
-------------------------------------------------------------------------------
makeEnv :: Types.GhcSrc -> Env 
makeEnv _ = RE {} 

-------------------------------------------------------------------------------
-- | Using the environment 
-------------------------------------------------------------------------------
class Resolve a where 
  resolve :: Env -> Types.ModName -> String -> Types.LocSymbol -> Either Types.UserError a 

instance Resolve Ghc.Var where 
  resolve = error "TBD:resolve (Var)"

-- | @strictResolve@ wraps the plain @resolve@ to throw an error 
--   if the name being searched for is unknown.
strictResolve :: (Resolve a) => Env -> Types.ModName -> String -> Types.LocSymbol -> a 
strictResolve env name x kind = case resolve env name x kind of 
  Left  err -> Types.uError err 
  Right val -> val 