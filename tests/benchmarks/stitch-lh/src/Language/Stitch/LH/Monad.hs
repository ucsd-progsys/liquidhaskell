{-# LANGUAGE GeneralizedNewtypeDeriving, DefaultSignatures,
             FlexibleContexts, MultiParamTypeClasses #-}

-- This is here to disable Liquid from tests.hs
{-# OPTIONS_GHC -fclear-plugins #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Monad
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- The Stitch monad, allowing for pretty-printed output to the user, failing
-- with an error message, and tracking global variables.
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Monad (
  -- * The 'Stitch' monad
  Stitch, runStitch, prompt, quit,

  -- * The 'StitchE' monad
  StitchE, runStitchE, issueError, eitherToStitchE,

  -- * General functions over both stitch monads
  StitchM(..),
  ) where

import Language.Stitch.LH.Check
import Language.Stitch.LH.Util

import System.Console.Haskeline

import Text.PrettyPrint.ANSI.Leijen

import Control.Monad.Trans.Maybe
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import System.IO

-- | A monad giving Haskeline-like interaction, access to 'Globals',
-- and the ability to abort with 'mzero'.
newtype Stitch a = Stitch { unStitch :: MaybeT (StateT Globals (InputT IO)) a }
  deriving (Monad, Functor, Applicative, MonadState Globals, MonadIO)

-- | Like the 'Stitch' monad, but also supporting error messages via 'Doc's
newtype StitchE a = StitchE { unStitchE :: ExceptT Doc Stitch a }
  deriving (Monad, Functor, Applicative, MonadError Doc)

instance MonadReader Globals StitchE where
  ask = StitchE get
  local f thing_inside = StitchE $ do
    old_globals <- get
    put (f old_globals)
    result <- unStitchE thing_inside
    put old_globals
    return result

-- | Class for the two stitchorous monads
class StitchM m where
  -- | Print a 'Doc' without a newline at the end
  printDoc :: Doc -> m ()

  -- | Print a 'Doc' with a newline
  printLine :: Doc -> m ()

instance StitchM Stitch where
  printDoc = Stitch . liftIO . displayIO stdout . toSimpleDoc
  printLine = Stitch . liftIO . displayIO stdout . toSimpleDoc . (<> hardline)

instance StitchM StitchE where
  printDoc = StitchE . lift . printDoc
  printLine = StitchE . lift . printLine

-- | Prompt the user for input, returning a string if one is entered.
-- Like 'getInputLine'.
prompt :: String -> Stitch (Maybe String)
prompt = Stitch . lift . lift . getInputLine

-- | Abort the 'Stitch' monad
quit :: Stitch a
quit = do
  printLine (text "Good-bye.")
  Stitch mzero

-- | Abort the computation with an error
issueError :: Doc -> StitchE a
issueError = StitchE . throwError

-- | Hoist an 'Either' into 'StitchE'
eitherToStitchE :: Either String a -> StitchE a
eitherToStitchE (Left err) = issueError (text err)
eitherToStitchE (Right x)  = return x

-- | Run a 'Stitch' computation
runStitch :: Stitch () -> InputT IO ()
runStitch thing_inside
  = void $ flip evalStateT emptyGlobals $ runMaybeT $ unStitch thing_inside

-- | Run a 'StitchE' computation
runStitchE :: StitchE a -> Stitch (Either Doc a)
runStitchE thing_inside
  = runExceptT $ unStitchE thing_inside
