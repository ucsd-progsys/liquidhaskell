module Language.Haskell.Liquid.Desugar.HscMain (hscDesugarWithLoc) where

import GHC	    (ModLocation, ParsedMod, TypecheckedMod)	
import TcRnTypes
import HscTypes
import MonadUtils
import ErrUtils
import Bag
import CoreMonad hiding (getHscEnv)
import Language.Haskell.Liquid.Desugar.Desugar (deSugarWithLoc)
import Exception

newtype Hsc a = Hsc (HscEnv -> WarningMessages -> IO (a, WarningMessages))

instance Monad Hsc where
    return a    = Hsc $ \_ w -> return (a, w)
    Hsc m >>= k = Hsc $ \e w -> do (a, w1) <- m e w
                                   case k a of
                                     Hsc k' -> k' e w1

instance MonadIO Hsc where
    liftIO io = Hsc $ \_ w -> do { a <- io; return (a, w) }

hscDesugarWithLoc :: HscEnv -> ModSummary -> TcGblEnv -> IO ModGuts
hscDesugarWithLoc hsc_env mod_summary tc_result =
  runHsc hsc_env $ hscDesugar' (ms_location mod_summary) tc_result

runHsc :: HscEnv -> Hsc a -> IO a
runHsc hsc_env (Hsc hsc) = do
    (a, w) <- hsc hsc_env emptyBag
    printOrThrowWarnings (hsc_dflags hsc_env) w
    return a

hscDesugar' :: ModLocation -> TcGblEnv -> Hsc ModGuts
hscDesugar' mod_location tc_result = do
  hsc_env <- getHscEnv
  r <- ioMsgMaybe $ {-# SCC "deSugar" #-} deSugarWithLoc hsc_env mod_location tc_result
  return r

ioMsgMaybe :: IO (Messages, Maybe a) -> Hsc a
ioMsgMaybe ioA = do
    ((warns,errs), mb_r) <- liftIO $ ioA
    logWarnings warns
    case mb_r of
        Nothing -> throwErrors errs
        Just r  -> {- ASSERT( isEmptyBag errs ) -} return r

logWarnings :: WarningMessages -> Hsc ()
logWarnings w = Hsc $ \_ w0 -> return ((), w0 `unionBags` w)

throwErrors :: ErrorMessages -> Hsc a
throwErrors = liftIO . throwIO . mkSrcErr

getHscEnv :: Hsc HscEnv
getHscEnv = Hsc $ \e w -> return (e, w)
