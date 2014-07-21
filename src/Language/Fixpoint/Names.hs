{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}

-- | This module contains Haskell variables representing globally visible names.
--   Rather than have strings floating around the system, all constant names
--   should be defined here, and the (exported) variables should be used and
--   manipulated elsewhere.

module Language.Fixpoint.Names (
  
  -- * Hardwired global names 
    dummyName
  , preludeName
  , boolConName
  , funConName
  , listConName
  , tupConName
  , propConName
  , strConName
  , vvName
  , symSepName
  , dropModuleNames 
  , takeModuleNames
) where

import qualified Data.Text      as T
import Data.Interned
import Data.Interned.Text

import Language.Fixpoint.Misc   (errorstar, stripParens)

----------------------------------------------------------------------------
--------------- Global Name Definitions ------------------------------------
----------------------------------------------------------------------------

preludeName, dummyName, boolConName, funConName, listConName, tupConName, propConName, strConName, vvName :: InternedText
preludeName  = "Prelude"
dummyName    = "_LIQUID_dummy"
boolConName  = "Bool"
funConName   = "->"
listConName  = "[]" -- "List"
tupConName   = "()" -- "Tuple"
propConName  = "Prop"
strConName   = "Str"
vvName       = "VV"
symSepName   = '#'

-- dropModuleNames []  = []
-- dropModuleNames s  
--   | s == tupConName = tupConName 
--   | otherwise       = safeLast msg $ words $ dotWhite `fmap` stripParens s
--   where 
--     msg             = "dropModuleNames: " ++ s 
--     dotWhite '.'    = ' '
--     dotWhite c      = c

dropModuleNames          = mungeModuleNames safeLast "dropModuleNames: "
takeModuleNames          = mungeModuleNames safeInit "takeModuleNames: "

safeInit :: String -> [T.Text] -> T.Text
safeInit _ xs@(_:_)      = T.intercalate "." $ init xs
safeInit msg _           = errorstar $ "safeInit with empty list " ++ msg

safeLast :: String -> [T.Text] -> T.Text
safeLast _ xs@(_:_)      = T.intercalate "." $ init xs
safeLast msg _           = errorstar $ "safeInit with empty list " ++ msg

mungeModuleNames :: (String -> [T.Text] -> T.Text) -> String -> T.Text -> T.Text
mungeModuleNames _ _ ""  = ""
mungeModuleNames f msg s  
  | s == unintern tupConName
   = unintern tupConName
  | otherwise            = f (msg ++ T.unpack s) $ T.words $ dotWhite `T.map` stripParens s
  where 
    dotWhite '.'         = ' '
    dotWhite c           = c

