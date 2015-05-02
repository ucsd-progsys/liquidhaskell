{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

-- | This module contains Haskell variables representing globally visible names.
--   Rather than have strings floating around the system, all constant names
--   should be defined here, and the (exported) variables should be used and
--   manipulated elsewhere.

module Language.Fixpoint.Names (

  -- * Symbols
    Symbol
  , Symbolic (..)
  , anfPrefix, tempPrefix, vv, intKvar, isPrefixOfSym, isSuffixOfSym, stripParensSym
  , consSym, unconsSym, dropSym, singletonSym, headSym, takeWhileSym, lengthSym
  , symChars, isNonSymbol, nonSymbol
  , isNontrivialVV
  , symbolText, symbolString
  , encode, vvCon
  , dropModuleNames
  , dropModuleUnique
  , takeModuleNames

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
  , hpropConName
  , strConName
  , vvName
  , symSepName
  , size32Name, size64Name, bitVecName, bvAndName, bvOrName
  , prims
) where

import           Control.Applicative
import           Control.DeepSeq
import           Data.Char
import           Data.Generics               (Data)
import           Data.Hashable
import qualified Data.HashSet                as S
import           Data.Interned
import           Data.Interned.Internal.Text
import           Data.Interned.Text
import           Data.Monoid
import           Data.String
import           Data.Text                   (Text)
import qualified Data.Text                   as T
import           Data.Typeable               (Typeable)
import           GHC.Generics                (Generic)

import           Language.Fixpoint.Misc      (errorstar, mapSnd, stripParens)

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
  hashWithSalt s (InternedText i t) = hashWithSalt s i

instance NFData InternedText where
  rnf (InternedText id t) = rnf id `seq` rnf t `seq` ()

instance Show Symbol where
  show (S x) = show x

instance NFData Symbol where
  rnf (S x) = rnf x

instance Hashable Symbol where
  hashWithSalt i (S s) = hashWithSalt i s

symbolString :: Symbol -> String
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

isPrefixOfSym (symbolText -> p) (symbolText -> x) = p `T.isPrefixOf` x
isSuffixOfSym (symbolText -> p) (symbolText -> x) = p `T.isSuffixOf` x
takeWhileSym p (symbolText -> t) = symbol $ T.takeWhile p t

headSym (symbolText -> t) = T.head t
consSym c (symbolText -> s) = symbol $ T.cons c s
singletonSym = (`consSym` "")

lengthSym (symbolText -> t) = T.length t

unconsSym :: Symbol -> Maybe (Char, Symbol)
unconsSym (symbolText -> s) = mapSnd symbol <$> T.uncons s

dropSym :: Int -> Symbol -> Symbol
dropSym n (symbolText -> t) = symbol $ T.drop n t

stripParensSym (symbolText -> t) = symbol $ stripParens t

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

qualifySymbol :: Symbol -> Symbol -> Symbol
qualifySymbol m'@(symbolText -> m) x'@(symbolText -> x)
  | isQualified x  = x'
  | isParened x    = symbol (wrapParens (m `mappend` "." `mappend` stripParens x))
  | otherwise      = symbol (m `mappend` "." `mappend` x)

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

intSymbol :: (Show a) => Symbol -> a -> Symbol 
intSymbol x i       = x `mappend` symbol (show i)

tempSymbol          :: Symbol -> Integer -> Symbol
tempSymbol prefix n = intSymbol (tempPrefix `mappend` prefix) n

tempPrefix, anfPrefix :: Symbol
tempPrefix          = "lq_tmp_"
anfPrefix           = "lq_anf_"

nonSymbol :: Symbol
nonSymbol           = ""
isNonSymbol         = (== nonSymbol)

intKvar             :: Integer -> Symbol
intKvar             = intSymbol "k_"

-- | Values that can be viewed as Symbols

class Symbolic a where
  symbol :: a -> Symbol

instance Symbolic String where
  symbol = symbol . T.pack

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
hpropConName = "HProp"
strConName   = "Str"
vvName       = "VV"
symSepName   = '#'

size32Name   = "Size32" :: Symbol
size64Name   = "Size64" :: Symbol
bitVecName   = "BitVec" :: Symbol
bvOrName     = "bvor"   :: Symbol
bvAndName    = "bvAnd"  :: Symbol

prims :: [Symbol]
prims = [ propConName
        , hpropConName
        , vvName
        , "Pred"
        , "List"
        , "Set_Set"
        , "Set_sng"
        , "Set_cup"
        , "Set_cap"
        , "Set_dif"
        , "Set_emp"
        , "Set_empty"
        , "Set_mem"
        , "Set_sub"
        , "Map_t"
        , "Map_select"
        , "Map_store"
        , size32Name
        , size64Name
        , bitVecName
        , bvOrName
        , bvAndName
        , "FAppTy"
        ]

-- dropModuleNames []  = []
-- dropModuleNames s
--   | s == tupConName = tupConName
--   | otherwise       = safeLast msg $ words $ dotWhite `fmap` stripParens s
--   where
--     msg             = "dropModuleNames: " ++ s
--     dotWhite '.'    = ' '
--     dotWhite c      = c

sepModNames = "."
sepUnique   = "#"

dropModuleNames          = mungeNames safeLast sepModNames "dropModuleNames: "
takeModuleNames          = mungeNames safeInit sepModNames "takeModuleNames: "

dropModuleUnique         = mungeNames safeHead sepUnique   "dropModuleUnique: "

safeHead :: String -> [T.Text] -> Symbol
safeHead msg [] = errorstar $ "safeHead with empty list" ++ msg
safeHead _ (x:_) = symbol x

safeInit :: String -> [T.Text] -> Symbol
safeInit _ xs@(_:_)      = symbol $ T.intercalate "." $ init xs
safeInit msg _           = errorstar $ "safeInit with empty list " ++ msg

safeLast :: String -> [T.Text] -> Symbol
safeLast _ xs@(_:_)      = symbol $ last xs
safeLast msg _           = errorstar $ "safeLast with empty list " ++ msg

mungeNames :: (String -> [T.Text] -> Symbol) -> T.Text -> String -> Symbol -> Symbol
mungeNames _ _ _ ""  = ""
mungeNames f d msg s'@(symbolText -> s)
  | s' == tupConName
  = tupConName
  | otherwise            = f (msg ++ T.unpack s) $ T.splitOn d $ stripParens s
