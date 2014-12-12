{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.RTEnv (
    makeRTEnv
  ) where

import Control.Applicative ((<$>))
import Control.Monad.State

import Language.Haskell.Liquid.Types

import qualified Language.Haskell.Liquid.Measure as Ms

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Misc (symbolRTyVar)
import Language.Haskell.Liquid.Bare.Reft
import Language.Haskell.Liquid.Bare.Type

--- Refinement Type Aliases
makeRTEnv specs
  = do forM_ rts $ \(mod, rta) -> setRTAlias (rtName rta) $ Left (mod, rta)
       forM_ pts $ \(mod, pta) -> setRPAlias (rtName pta) $ Left (mod, pta)
       forM_ ets $ \(mod, eta) -> setREAlias (rtName eta) $ Left (mod, eta)
       makeREAliases ets
       makeRPAliases pts
       makeRTAliases rts
    where
       rts = (concat [(m,) <$> Ms.aliases  s | (m, s) <- specs])
       pts = (concat [(m,) <$> Ms.paliases s | (m, s) <- specs])
       ets = (concat [(m,) <$> Ms.ealiases s | (m, s) <- specs])
       
makeRTAliases xts = mapM_ expBody xts
  where
    expBody (mod,xt) = inModule mod $ do
                             let l = rtPos xt
                             body <- withVArgs l (rtVArgs xt) $ ofBareType l $ rtBody xt
                             setRTAlias (rtName xt) $ Right $ mapRTAVars symbolRTyVar $ xt { rtBody = body }

makeRPAliases xts     = mapM_ expBody xts
  where 
    expBody (mod, xt) = inModule mod $ do
                          let l = rtPos xt
                          body <- withVArgs l (rtVArgs xt) $ expandPred l $ rtBody xt
                          setRPAlias (rtName xt) $ Right $ xt { rtBody = body }

makeREAliases xts     = mapM_ expBody xts
  where 
    expBody (mod, xt) = inModule mod $ do
                          let l = rtPos xt
                          body <- withVArgs l (rtVArgs xt) $ expandExpr l $ rtBody xt
                          setREAlias (rtName xt) $ Right $ xt { rtBody = body }

