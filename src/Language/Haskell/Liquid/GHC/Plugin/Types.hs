 
{-# LANGUAGE DeriveDataTypeable #-}

module Language.Haskell.Liquid.GHC.Plugin.Types
    ( SpecComment(..)
    ) where

import Data.Data (Data)
import Text.Parsec (SourcePos)

newtype SpecComment =
    SpecComment (SourcePos, String)
    deriving Data

