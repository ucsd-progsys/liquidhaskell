{-# LANGUAGE OverloadedStrings #-}

module Language.Haskell.Liquid.Types.Names where

import Language.Fixpoint.Types


lenLocSymbol = dummyLoc $ symbol ("autolen" :: String)


arrowConName, runFunName :: Symbol
arrowConName = "Arrow"
runFunName   = "runFun"

arrowFTyCon = symbolFTycon $ dummyLoc arrowConName
