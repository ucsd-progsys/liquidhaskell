-------------------------------------------------------------------------------
--
-- | Main API for compiling plain Haskell source code.
--
-- This module implements compilation of a Haskell source. It is
-- /not/ concerned with preprocessing of source files; this is handled
-- in "DriverPipeline".
--
-- There are various entry points depending on what mode we're in:
-- "batch" mode (@--make@), "one-shot" mode (@-c@, @-S@ etc.), and
-- "interactive" mode (GHCi). There are also entry points for
-- individual passes: parsing, typechecking/renaming, desugaring, and
-- simplification.
--
-- All the functions here take an 'HscEnv' as a parameter, but none of
-- them return a new one: 'HscEnv' is treated as an immutable value
-- from here on in (although it has mutable components, for the
-- caches).
--
-- Warning messages are dealt with consistently throughout this API:
-- during compilation warnings are collected, and before any function
-- in @HscMain@ returns, the warnings are either printed, or turned
-- into a real compialtion error if the @-Werror@ flag is enabled.
--
-- (c) The GRASP/AQUA Project, Glasgow University, 1993-2000
--
-------------------------------------------------------------------------------

module Language.Haskell.Liquid.Desugar.HscMain (hscDesugarWithLoc) where

import Language.Haskell.Liquid.Desugar.Desugar (deSugarWithLoc)

import Module 
import Packages
import RdrName
import HsSyn
import CoreSyn
import StringBuffer
import Parser
import Lexer
import SrcLoc
import TcRnDriver
import TcIface          ( typecheckIface )
import TcRnMonad
import IfaceEnv         ( initNameCache )
import LoadIface        ( ifaceStats, initExternalPackageState )
import PrelInfo
import MkIface
import SimplCore
import TidyPgm
import CorePrep
import CoreToStg        ( coreToStg )
import qualified StgCmm ( codeGen )
import StgSyn
import CostCentre
import ProfInit
import TyCon
import Name
import SimplStg         ( stg2stg )
import Cmm
import CmmParse         ( parseCmmFile )
import CmmBuildInfoTables
import CmmPipeline
import CmmInfo
import CodeOutput
import NameEnv          ( emptyNameEnv )
import NameSet          ( emptyNameSet )
import InstEnv
import FamInstEnv
import Fingerprint      ( Fingerprint )
import Hooks

import DynFlags
import ErrUtils

import Outputable
import HscStats         ( ppSourceStats )
import HscTypes
import MkExternalCore   ( emitExternalCore )
import FastString
import UniqFM           ( emptyUFM )
import UniqSupply
import Bag
import Exception
import qualified Stream
import Stream (Stream)

import Util

import Data.List
import Control.Monad
import Data.Maybe
import Data.IORef
import System.FilePath as FilePath
import System.Directory


-- -----------------------------------------------------------------------------

getWarnings :: Hsc WarningMessages
getWarnings = Hsc $ \_ w -> return (w, w)

clearWarnings :: Hsc ()
clearWarnings = Hsc $ \_ _ -> return ((), emptyBag)

logWarnings :: WarningMessages -> Hsc ()
logWarnings w = Hsc $ \_ w0 -> return ((), w0 `unionBags` w)


-- | log warning in the monad, and if there are errors then
-- throw a SourceError exception.
logWarningsReportErrors :: Messages -> Hsc ()
logWarningsReportErrors (warns,errs) = do
    logWarnings warns
    when (not $ isEmptyBag errs) $ throwErrors errs

-- | Throw some errors.
throwErrors :: ErrorMessages -> Hsc a
throwErrors = liftIO . throwIO . mkSrcErr

-- 
-- | Convert a typechecked module to Core
hscDesugarWithLoc :: HscEnv -> ModSummary -> TcGblEnv -> IO ModGuts
hscDesugarWithLoc hsc_env mod_summary tc_result =
    runHsc hsc_env $ hscDesugar' (ms_location mod_summary) tc_result

hscDesugar' :: ModLocation -> TcGblEnv -> Hsc ModGuts
hscDesugar' mod_location tc_result = do
    hsc_env <- getHscEnv
    r <- ioMsgMaybe $
      {-# SCC "deSugar" #-}
      deSugarWithLoc hsc_env mod_location tc_result

    -- always check -Werror after desugaring, this is the last opportunity for
    -- warnings to arise before the backend.
    handleWarnings
    return r

getHscEnv :: Hsc HscEnv
getHscEnv = Hsc $ \e w -> return (e, w)

handleWarnings :: Hsc ()
handleWarnings = do
    dflags <- getDynFlags
    w <- getWarnings
    liftIO $ printOrThrowWarnings dflags w
    clearWarnings

ioMsgMaybe :: IO (Messages, Maybe a) -> Hsc a
ioMsgMaybe ioA = do
    ((warns,errs), mb_r) <- liftIO ioA
    logWarnings warns
    case mb_r of
        Nothing -> throwErrors errs
        Just r  -> return r
