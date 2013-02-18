{-# LANGUAGE ScopedTypeVariables #-}

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
  , vvName
  , symSepName
  , dropModuleNames 
) where

import Language.Fixpoint.Misc (safeLast, stripParens)

----------------------------------------------------------------------------
--------------- Global Name Definitions ------------------------------------
----------------------------------------------------------------------------

preludeName  = "Prelude"
dummyName    = "_LIQUID_dummy"
boolConName  = "Bool"
funConName   = "->"
listConName  = "[]" -- "List"
tupConName   = "()" -- "Tuple"

propConName  = "Prop"
vvName       = "VV"
symSepName   = '#'

dropModuleNames []  = []
dropModuleNames s  
  | s == tupConName = tupConName 
  | otherwise       = safeLast msg $ words $ dotWhite `fmap` stripParens s
  where 
    msg             = "dropModuleNames: " ++ s 
    dotWhite '.'    = ' '
    dotWhite c      = c


