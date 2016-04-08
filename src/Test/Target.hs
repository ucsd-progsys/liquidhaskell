{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Test.Target
  ( target, targetResult, targetWith, targetResultWith
  , targetTH, targetResultTH, targetWithTH, targetResultWithTH
  , Result(..), Testable, Targetable(..)
  , TargetOpts(..), defaultOpts
  , Test(..)
  , monomorphic
  ) where


import           Control.Applicative
import           Control.Arrow
import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.State
import qualified Language.Haskell.TH             as TH
import           System.Process                  (terminateProcess)
import           Test.QuickCheck.All             (monomorphic)
import           Text.Printf                     (printf)

import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Smt.Interface hiding (verbose)

import           Test.Target.Monad
import           Test.Target.Targetable (Targetable(..))
import           Test.Target.Targetable.Function ()
import           Test.Target.Testable
import           Test.Target.Types
import           Test.Target.Util

-- | Test whether a function inhabits its refinement type by enumerating valid
-- inputs and calling the function.
target :: Testable f
       => f -- ^ the function
       -> String -- ^ the name of the function
       -> FilePath -- ^ the path to the module that defines the function
       -> IO ()
target f name path
  = targetWith f name path defaultOpts

targetTH :: TH.Name -> FilePath -> TH.ExpQ
targetTH f m = [| target $(monomorphic f) $(TH.stringE $ show f) m |]

-- targetTH :: TH.ExpQ -- (TH.TExp (Testable f => f -> TH.Name -> IO ()))
-- targetTH = TH.location >>= \TH.Loc {..} ->
--   [| \ f n -> target f (show n) loc_filename |]

-- | Like 'target', but returns the 'Result' instead of printing to standard out.
targetResult :: Testable f => f -> String -> FilePath -> IO Result
targetResult f name path
  = targetResultWith f name path defaultOpts

targetResultTH :: TH.Name -> FilePath -> TH.ExpQ
targetResultTH f m = [| targetResult $(monomorphic f) $(TH.stringE $ show f) m |]

-- | Like 'target', but accepts options to control the enumeration depth,
-- solver, and verbosity.
targetWith :: Testable f => f -> String -> FilePath -> TargetOpts -> IO ()
targetWith f name path opts
  = do res <- targetResultWith f name path opts
       case res of
         Passed n -> printf "OK. Passed %d tests\n\n" n
         Failed x -> printf "Found counter-example: %s\n\n" x
         Errored x -> printf "Error! %s\n\n" x

targetWithTH :: TH.Name -> FilePath -> TargetOpts -> TH.ExpQ
targetWithTH f m opts = [| targetWith $(monomorphic f) $(TH.stringE $ show f) m opts |]

-- | Like 'targetWith', but returns the 'Result' instead of printing to standard out.
targetResultWith :: Testable f => f -> String -> FilePath -> TargetOpts -> IO Result
targetResultWith f name path opts
  = do when (verbose opts) $
         printf "Testing %s\n" name
       sp  <- getSpec (ghcOpts opts) path
       ctx <- mkContext (solver opts)
       do r <- runTarget opts (initState path sp ctx undefined) $ do
                 ty <- safeFromJust "targetResultWith" . lookup (symbol name) <$> gets sigs
                 test f ty
          _ <- cleanupContext ctx
          return r
        `onException` terminateProcess (pId ctx)
  where
    mkContext = if logging opts
                then flip (makeContext False) (".target/" ++ name)
                else makeContextNoLog False

targetResultWithTH :: TH.Name -> FilePath -> TargetOpts -> TH.ExpQ
targetResultWithTH f m opts = [| targetResultWith $(monomorphic f) $(TH.stringE $ show f) m opts |]

data Test = forall t. Testable t => T t
