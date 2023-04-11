{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances  #-}

module Language.Haskell.Liquid.Interactive.Types
  (
    -- * Commands
    Command

    -- * Response
  , Response

  , status

    -- * State
  , State (..)

  ) where

import Prelude        hiding (error)
import Data.Serialize        ( Serialize )
import GHC.Generics
import System.Console.CmdArgs
import System.Exit
import Language.Haskell.Liquid.Types (Config (..))
import Language.Haskell.Liquid.Liquid
import Language.Fixpoint.Types ()

-------------------------------------------------------------------------------
-- | State --------------------------------------------------------------------
-------------------------------------------------------------------------------

data State = State { sCount  :: Int
                   , sMbEnv :: MbEnv
                   }

-------------------------------------------------------------------------------
-- | Command ------------------------------------------------------------------
-------------------------------------------------------------------------------

type Command = Config

-------------------------------------------------------------------------------
-- | Response -----------------------------------------------------------------
-------------------------------------------------------------------------------

data Status = ResOk
            | ResFail Int
               deriving ( Generic, Data, Typeable, Show )

type Response = (Status, Int)

instance Serialize Status

status :: ExitCode -> Status
status ExitSuccess     = ResOk
status (ExitFailure n) = ResFail n
