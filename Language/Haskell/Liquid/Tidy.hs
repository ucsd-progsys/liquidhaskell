{-# LANGUAGE NoMonomorphismRestriction, DeriveDataTypeable, RankNTypes, GADTs, TupleSections  #-}

module Language.Haskell.Liquid.Tidy (tidy) where

import Data.Generics.Schemes
import Data.Generics.Aliases
import Data.Data
import Control.Monad.State
import qualified Data.Map as M

data TidyS = T { memo :: M.Map String String
               , pool :: [String] }

type TidyM = State TidyS

sel :: String -> TidyM (Maybe String)
sel s 
  = ((s `M.lookup`) . memo) `fmap` get 

upd ::  String -> TidyM String
upd s 
  = do st <- get
       let (s':t) = pool st
       let m      = memo st
       put $ st {memo = M.insert s s' m, pool = t}
       return s'

rename :: String -> TidyM String
rename s 
  = do so <- sel s
       case so of 
         Just s' -> return s'
         Nothing -> upd s 

cleaner getS putS = everywhereM (mkM swiz)
  where swiz x = case getS x of 
                   Nothing -> return x
                   Just s  -> liftM (putS x) (rename s)

tidy :: (Data b, Typeable a) => [String] -> (a -> Maybe String) -> (a -> String -> a) -> b -> b 
tidy pool0 getS putS z = fst $ runState act s0
  where act      = cleaner getS putS z 
        s0       = T { memo = M.empty, pool = pool0 }
