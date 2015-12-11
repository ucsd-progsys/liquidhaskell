{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances  #-}

module Language.Haskell.Liquid.Interactive.Types
  (
    -- * Commands
    Command (..)

    -- * Response
  , Response (..)
  , response
  
    -- * State
  , State (..)

  ) where

-- import Data.ByteString.Char8 ( ByteString )
import Data.Serialize        ( Serialize )
import GHC.Generics
import System.Console.CmdArgs
import System.Exit
import Language.Haskell.Liquid.Types (Config (..))
import Language.Fixpoint.Types () -- -- (Error, FixResult (..))

-- import qualified Data.HashMap.Strict as M

-------------------------------------------------------------------------------
-- | State --------------------------------------------------------------------
-------------------------------------------------------------------------------

data State = State { sCount :: Int }

-------------------------------------------------------------------------------
-- | Command ------------------------------------------------------------------
-------------------------------------------------------------------------------

type Command = Config

-------------------------------------------------------------------------------
-- | Response -----------------------------------------------------------------
-------------------------------------------------------------------------------

data Response = ResOk
              | ResFail Int
               deriving ( Generic, Data, Typeable, Show )

instance Serialize Response


response :: ExitCode -> Response
response ExitSuccess     = ResOk
response (ExitFailure n) = ResFail n

{-
cGet :: Command
cGet = CmdCheck { key  = def    &= help "Key to lookup"
           , port = 7856   &= help "Port at which to listen"
           } &= help    "Return value of given key"

cSet :: Command
cSet = Put { key = def     &= help "Key to update"
           , val = def     &= help "New value to update key to"
           , port = 7856   &= help "Port at which to listen"
           } &= help    "Update value of given key"

config :: Command
config = modes [ cGet &= auto
               , cSet
               ]
           &= help    "lhi is an interactive server for LiquidHaskell"
           &= program "lhi"
           &= summary "lhi © Copyright 2015 Regents of the University of California."
           &= verbosity
-}
