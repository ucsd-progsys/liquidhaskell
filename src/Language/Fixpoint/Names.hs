{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | This module contains Haskell variables representing globally visible names.
--   Rather than have strings floating around the system, all constant names
--   should be defined here, and the (exported) variables should be used and
--   manipulated elsewhere.

module Language.Fixpoint.Names (

  -- * Symbols
    Symbol(..)
  , Symbolic (..)
  , anfPrefix, tempPrefix, vv, intKvar
  , symChars, isNonSymbol, nonSymbol
  , isNontrivialVV
  , symbolText, symbolString
  , encode, vvCon

  -- * Creating Symbols
  , dummySymbol, intSymbol, tempSymbol
  , qualifySymbol
  , suffixSymbol

  -- * Hardwired global names 
  , dummyName
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

import GHC.Generics         (Generic)
import Data.Char
import Data.String
import Data.Typeable        (Typeable)
import Data.Generics        (Data)
import Data.Text                (Text)
import qualified Data.Text      as T
import Data.Monoid
import Data.Interned
import Data.Interned.Internal.Text
import Data.Interned.Text
import Data.Hashable
import qualified Data.HashSet        as S
import Control.DeepSeq

import Language.Fixpoint.Misc   (errorstar, stripParens)

---------------------------------------------------------------
---------------------------- Symbols --------------------------
---------------------------------------------------------------

symChars
  =  ['a' .. 'z']
  ++ ['A' .. 'Z']
  ++ ['0' .. '9']
  ++ ['_', '%', '.', '#']

deriving instance Data InternedText
deriving instance Typeable InternedText
deriving instance Generic InternedText

newtype Symbol = S InternedText deriving (Eq, Ord, Data, Typeable, Generic, IsString)

instance Monoid Symbol where
  mempty      = ""
  mappend x y = S . intern $ mappend (symbolText x) (symbolText y)

instance Hashable InternedText where
  hashWithSalt s it = hashWithSalt s (unintern it)

instance NFData InternedText where
  rnf (InternedText id t) = rnf id `seq` rnf t

instance Show Symbol where
  show (S x) = show x

symbolString = T.unpack . symbolText

---------------------------------------------------------------------------
------ Converting Strings To Fixpoint -------------------------------------
---------------------------------------------------------------------------

-- stringSymbolRaw :: String -> Symbol
-- stringSymbolRaw = S

encode :: String -> String
encode s
  | isFixKey  s = encodeSym s
  | isFixSym' s = s
  | otherwise   = encodeSym s -- S $ fixSymPrefix ++ concatMap encodeChar s

encodeSym s     = fixSymPrefix ++ concatMap encodeChar s

symbolText :: Symbol -> Text
symbolText (S s) = unintern s

-- symbolString :: Symbol -> String
-- symbolString (S str)
--   = case chopPrefix fixSymPrefix str of
--       Just s  -> concat $ zipWith tx indices $ chunks s
--       Nothing -> str
--     where
--       chunks = unIntersperse symSepName
--       tx i s = if even i then s else [decodeStr s]

indices :: [Integer]
indices = [0..]

okSymChars
  = S.fromList
   $ ['a' .. 'z']
  ++ ['A' .. 'Z']
  ++ ['0' .. '9']
  ++ ['_', '.'  ]

fixSymPrefix = "fix" ++ [symSepName]

suffixSymbol (S s) suf = symbol $ (unintern s) `mappend` suf

isFixSym' (c:chs)  = isAlpha c && all (`S.member` (symSepName `S.insert` okSymChars)) chs
isFixSym' _        = False

isFixKey x = S.member x keywords
keywords   = S.fromList ["env", "id", "tag", "qualif", "constant", "cut", "bind", "constraint", "grd", "lhs", "rhs"]

encodeChar c
  | c `S.member` okSymChars
  = [c]
  | otherwise
  = [symSepName] ++ (show $ ord c) ++ [symSepName]

decodeStr s
  = chr ((read s) :: Int)

qualifySymbol :: Text -> Symbol -> Symbol
qualifySymbol x (S sy)
  | isQualified x' = S sy
  | isParened x'   = symbol (wrapParens (x `mappend` "." `mappend` stripParens x'))
  | otherwise      = symbol (x `mappend` "." `mappend` x')
  where x' = unintern sy

isQualified y         = "." `T.isInfixOf` y
wrapParens x          = "(" `mappend` x `mappend` ")"
isParened xs          = xs /= stripParens xs

---------------------------------------------------------------------

vv                  :: Maybe Integer -> Symbol
vv (Just i)         = symbol $ symbolText vvName `T.snoc` symSepName `mappend` T.pack (show i) --  S (vvName ++ [symSepName] ++ show i)
vv Nothing          = vvName

vvCon               = symbol $ symbolText vvName `T.snoc` symSepName `mappend` "F" --  S (vvName ++ [symSepName] ++ "F")

isNontrivialVV      = not . (vv Nothing ==)


dummySymbol         = dummyName
intSymbol x i       = symbol $ x `mappend` T.pack (show i)

tempSymbol          :: Text -> Integer -> Symbol
tempSymbol prefix n = intSymbol (tempPrefix `mappend` prefix) n

tempPrefix          = "lq_tmp_"
anfPrefix           = "lq_anf_"
nonSymbol           = S ""
isNonSymbol         = (== nonSymbol)

intKvar             :: Integer -> Symbol
intKvar             = intSymbol "k_"

-- | Values that can be viewed as Symbols

class Symbolic a where
  symbol :: a -> Symbol

instance Symbolic Text where
  symbol = S . intern

instance Symbolic InternedText where
  symbol = S

instance Symbolic Symbol where
  symbol = id


----------------------------------------------------------------------------
--------------- Global Name Definitions ------------------------------------
----------------------------------------------------------------------------

preludeName, dummyName, boolConName, funConName, listConName, tupConName, propConName, strConName, vvName :: Symbol
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
  | s == symbolText tupConName
   = symbolText tupConName
  | otherwise            = f (msg ++ T.unpack s) $ T.words $ dotWhite `T.map` stripParens s
  where 
    dotWhite '.'         = ' '
    dotWhite c           = c

