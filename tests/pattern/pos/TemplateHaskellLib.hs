{-# LANGUAGE TemplateHaskell #-}

module TemplateHaskellLib where

import Language.Haskell.TH.Syntax

foo :: Q Exp
foo = [| 1 + 2|]

bar :: Q [Dec]
bar = do
  Just varName <- lookupValueName "hello"
  return  [SigD varName $ ConT $ mkName "String"]

