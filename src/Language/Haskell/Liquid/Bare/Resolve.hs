-- | This module has the code that uses the GHC definitions to:
--   1. MAKE a name-resolution environment,
--   2. USE the environment to translate plain symbols into Var, TyCon, etc. 

{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}

module Language.Haskell.Liquid.Bare.Resolve 
  ( -- * Creating the Environment
    makeEnv 

    -- * Resolving symbols 
  , ResolveSym (..)
  , strictResolveSym 

  , Qualify (..)

    -- * Resolving types etc. 
  , Resolvable (..)

  -- * Misc 
  , resolveNamedVar 

  ) where 

import qualified Var                             as Ghc
import qualified Module                          as Ghc
import qualified GHC                             as Ghc
import qualified Language.Fixpoint.Types         as F 
import           Language.Haskell.Liquid.Types   
import qualified Language.Haskell.Liquid.Measure as Ms
import           Language.Haskell.Liquid.Bare.Types 

-------------------------------------------------------------------------------
-- | Qualify various names 
-------------------------------------------------------------------------------
class Qualify a where 
  qualify :: Env -> ModName -> a -> a 

instance Qualify F.Symbol where 
  qualify env name x = case resolveSym env name "Symbol" x of 
    Left  _   -> x 
    Right val -> val 

instance Qualify LocSymbol where 
  qualify env name lx = qualify env name <$> lx 

instance Qualify SizeFun where 
  qualify env name (SymSizeFun lx) = SymSizeFun (qualify env name lx)
  qualify _   _    sf              = sf

instance Qualify TyConInfo where 
  qualify env name tci = tci { sizeFunction = qualify env name <$> sizeFunction tci }

instance Qualify RTyCon where 
  qualify env name rtc = rtc { rtc_info = qualify env name $ rtc_info rtc }


-------------------------------------------------------------------------------
-- | Creating an environment 
-------------------------------------------------------------------------------
makeEnv :: GhcSrc -> [(ModName, Ms.BareSpec)] -> LogicMap -> Env 
makeEnv _src specs lmap = RE 
  { reLMap  = lmap
  , reSyms  = undefined 
  , reSpecs = specs 
  } 

-------------------------------------------------------------------------------
resolveNamedVar :: (Ghc.NamedThing a) => Env -> ModName -> a -> Ghc.Var
-------------------------------------------------------------------------------
resolveNamedVar = undefined 

-------------------------------------------------------------------------------
-- | Using the environment 
-------------------------------------------------------------------------------
class ResolveSym a where 
  resolveLocSym :: Env -> ModName -> String -> LocSymbol -> Either UserError a 
  
instance ResolveSym Ghc.Var where 
  resolveLocSym = error "TBD:resolve (Var)"

instance ResolveSym Ghc.TyCon where 
  resolveLocSym = error "TBD:resolve (TyCon)"

instance ResolveSym F.Symbol where 
  resolveLocSym = error "TBD:resolve (Symbol)"
-- REBARE: qualifySymbol :: Env -> F.Symbol -> F.Symbol
-- REBARE: qualifySymbol env x = maybe x F.symbol (M.lookup x syms)
 
resolveSym :: (ResolveSym a) => Env -> ModName -> String -> F.Symbol -> Either UserError a 
resolveSym env name kind x = resolveLocSym env name kind (F.dummyLoc x) 

-- | @strictResolve@ wraps the plain @resolve@ to throw an error 
--   if the name being searched for is unknown.
strictResolveSym :: (ResolveSym a) => Env -> ModName -> String -> LocSymbol -> a 
strictResolveSym env name x kind = case resolveLocSym env name x kind of 
  Left  err -> uError err 
  Right val -> val 

class Resolvable a where 
  resolve :: Env -> ModName -> F.SourcePos -> a -> a  

instance Resolvable F.Qualifier where 
  resolve = undefined 