{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Tests.Util
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- Utility definnitions for testing stitch
--
----------------------------------------------------------------------------

module Tests.Util (
  module Test.Tasty,
  testCase,
  (@?=), (@=?), (@?) )
  where

import Language.Stitch.LH.Util

import Test.Tasty
import Test.Tasty.HUnit ( testCase, (@?), Assertion )

import Text.PrettyPrint.ANSI.Leijen

import Text.Parsec ( ParseError )

import Data.Function
import Language.Haskell.TH
import Control.Monad

prettyError :: Pretty a => a -> a -> String
prettyError exp act = (render $ text "Expected" <+> squotes (pretty exp) <> semi <+>
                                text "got" <+> squotes (pretty act))

(@?=) :: (Eq a, Pretty a) => a -> a -> Assertion
act @?= exp = (act == exp) @? prettyError exp act

(@=?) :: (Eq a, Pretty a) => a -> a -> Assertion
exp @=? act = (act == exp) @? prettyError exp act

$( do decs <- reifyInstances ''Eq [ConT ''ParseError]
      case decs of  -- GHC 7.6 eagerly typechecks the instance, sometimes
                    -- reporting a duplicate. Urgh. So we can't quote it.
        [] -> liftM (:[]) $
              instanceD (return []) (appT (conT ''Eq) (conT ''ParseError))
                        [ valD (varP '(==)) (normalB [| (==) `on` show |]) [] ]
        _  -> return [] )

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty (Left x)  = text "Left" <+> pretty x
  pretty (Right x) = text "Right" <+> pretty x
