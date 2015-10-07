{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE CPP                        #-}


-- | This module contains Haskell variables representing globally visible names.
--   Rather than have strings floating around the system, all constant names
--   should be defined here, and the (exported) variables should be used and
--   manipulated elsewhere.

module Language.Fixpoint.Names (

  -- * Symbols
    Symbol
  , Symbolic (..)

  -- * Conversion to/from Text
  , symbolSafeText
  , symbolSafeString
  , unsafeTextSymbol -- TODO: deprecate!

  -- Predicates
  , isPrefixOfSym
  , isSuffixOfSym
  , isNonSymbol
  , isNontrivialVV

  -- * Destructors
  , stripParensSym
  , stripPrefix
  , consSym
  , unconsSym
  , dropSym
  , singletonSym
  , headSym
  , takeWhileSym
  , lengthSym

  -- * Transforms
  , nonSymbol
  , vvCon

  -- , dropModuleNames
  -- , dropModuleUnique
  -- , takeModuleNames

  -- * Widely used prefixes
  , anfPrefix
  , litPrefix
  , tempPrefix
  , vv
  , symChars

  -- * Creating Symbols
  , dummySymbol
  , intSymbol
  , tempSymbol
  , existSymbol
  , renameSymbol
  , qualifySymbol

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
  , nilName
  , consName
  , vvName
  , symSepName
  , size32Name
  , size64Name
  , bitVecName
  , bvAndName
  , bvOrName
  , prims

) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative ((<$>))
import           Data.Monoid (Monoid (..))
#endif

import           Control.DeepSeq             (NFData (..))
import           Control.Arrow               (second)
import           Control.Monad               ((>=>))
import           Data.Char                   (isAlpha, chr, ord)
import           Data.Generics               (Data)
import           Data.Hashable               (Hashable (..))
import qualified Data.HashSet                as S
import           Data.Interned               (intern, unintern)
import           Data.Interned.Internal.Text
import           Data.Maybe                  (fromMaybe)
import           Data.String                 (IsString(..))
import qualified Data.Text                   as T
import           Data.Binary                 (Binary (..))
import           Data.Typeable               (Typeable)
import           GHC.Generics                (Generic)

import           Language.Fixpoint.Misc      (errorstar)


---------------------------------------------------------------
-- | Symbols --------------------------------------------------
---------------------------------------------------------------


deriving instance Data     InternedText
deriving instance Typeable InternedText
deriving instance Generic  InternedText

{-@ type SafeText = {v: T.Text | IsSafe v} @-}
type SafeText = T.Text

-- | Invariant: a `SafeText` is made up of:
--
--     ['0'..'9'] ++ ['a'...'z'] ++ ['A'..'Z'] ++ '$'
--
--   If the original text has ANY other chars, it is represented as:
--
--     lq$i
--
--   where i is a unique integer (for each text)

newtype Symbol = S InternedText deriving (Eq, Ord, Data, Typeable, Generic)

instance IsString Symbol where
  fromString = symbol

instance Monoid Symbol where
  mempty        = ""
  mappend s1 s2 = safeTextSymbol $ safeCat (symbolSafeText s1) (symbolSafeText s2)

-- instance Eq Symbol where
  -- s == s' = internal s == internal s'
--
-- instance Ord Symbol where
  -- compare s s' = compare (internal s) (internal s')

instance Hashable InternedText where
  hashWithSalt s (InternedText i _) = hashWithSalt s i

instance NFData InternedText where
  rnf (InternedText i t) = rnf i `seq` rnf t `seq` ()

instance Show Symbol where
  show (S x) = show x

instance NFData Symbol where
  rnf (S x)  = rnf x

instance Hashable Symbol where
  hashWithSalt i (S x) = hashWithSalt i x

instance Binary Symbol where
  get = safeTextSymbol <$> get  -- FIXME: serializing ERASES original external-text
  put = put . symbolSafeText

symbolSafeString :: Symbol -> String
symbolSafeString = T.unpack . symbolSafeText

symbolSafeText :: Symbol -> SafeText
symbolSafeText (S s) = unintern s

safeTextSymbol :: SafeText -> Symbol
safeTextSymbol = S . intern

unsafeTextSymbol :: T.Text -> Symbol
unsafeTextSymbol = safeTextSymbol -- FIXME: nasty ~A business for qualifier params. Sigh.

safeCat :: SafeText -> SafeText -> SafeText
safeCat = mappend

---------------------------------------------------------------------------
------ Converting Strings To Fixpoint -------------------------------------
---------------------------------------------------------------------------


-- INVARIANT: All strings *must* be built from here
toSymbol :: T.Text -> Symbol
toSymbol = S . intern . encode

encode :: T.Text -> SafeText
encode t
  | isSafeText t   = t
  | otherwise      = safeCat "enc$" (i2t i)
  where
  InternedText i _ = intern t
  i2t              = T.pack . show

isSafeText :: T.Text -> Bool
isSafeText t = T.all (`S.member` okSymChars) t && not (isFixKey t)

isFixKey :: T.Text -> Bool
isFixKey x = S.member x keywords

keywords :: S.HashSet T.Text
keywords   = S.fromList [ "env"
                        , "id"
                        , "tag"
                        , "qualif"
                        , "constant"
                        , "cut"
                        , "bind"
                        , "constraint"
                        , "lhs"
                        , "rhs"]


symChars :: [Char]
symChars
  =  ['a' .. 'z']
  ++ ['A' .. 'Z']
  ++ ['0' .. '9']
  ++ ['_' ,  '.']

okSymChars = S.fromList symChars

isPrefixOfSym :: Symbol -> Symbol -> Bool
isPrefixOfSym (symbolSafeText -> p) (symbolSafeText -> x) = p `T.isPrefixOf` x

isSuffixOfSym :: Symbol -> Symbol -> Bool
isSuffixOfSym (symbolSafeText -> p) (symbolSafeText -> x) = p `T.isSuffixOf` x

takeWhileSym :: (Char -> Bool) -> Symbol -> Symbol
takeWhileSym p (symbolSafeText -> t) = symbol $ T.takeWhile p t

headSym :: Symbol -> Char
headSym (symbolSafeText -> t) = T.head t

consSym :: Char -> Symbol -> Symbol
consSym c (symbolSafeText -> s) = symbol $ T.cons c s

unconsSym :: Symbol -> Maybe (Char, Symbol)
unconsSym (symbolSafeText -> s) = second symbol <$> T.uncons s

singletonSym :: Char -> Symbol -- Yuck
singletonSym = (`consSym` "")

lengthSym :: Symbol -> Int
lengthSym (symbolSafeText -> t) = T.length t

dropSym :: Int -> Symbol -> Symbol
dropSym n (symbolSafeText -> t) = symbol $ T.drop n t

stripParens :: T.Text -> T.Text
stripParens t = fromMaybe t (strip t)
  where
    strip = T.stripPrefix "(" >=> T.stripSuffix ")"

stripParensSym :: Symbol -> Symbol
stripParensSym (symbolSafeText -> t) = symbol $ stripParens t

stripPrefix :: Symbol -> Symbol -> Maybe Symbol
stripPrefix p x = safeTextSymbol <$> T.stripPrefix (symbolSafeText p) (symbolSafeText x)

qualifySymbol :: Symbol -> Symbol -> Symbol
qualifySymbol m'@(symbolSafeText -> m) x'@(symbolSafeText -> x)
  | isQualified x  = x'
  | isParened x    = symbol (wrapParens (m `mappend` "." `mappend` stripParens x))
  | otherwise      = symbol (m `mappend` "." `mappend` x)

isQualified y         = "." `T.isInfixOf` y
wrapParens x          = "(" `mappend` x `mappend` ")"
isParened xs          = xs /= stripParens xs

---------------------------------------------------------------------

vv                  :: Maybe Integer -> Symbol
vv (Just i)         = symbol $ symbolSafeText vvName `T.snoc` symSepName `mappend` T.pack (show i) --  S (vvName ++ [symSepName] ++ show i)
vv Nothing          = vvName

-- vvCon               = symbol $ symbolSafeText vvName `T.snoc` symSepName `mappend` "F" --  S (vvName ++ [symSepName] ++ "F")

isNontrivialVV      = not . (vv Nothing ==)

vvCon, dummySymbol :: Symbol
vvCon       = vvName `mappend` symbol [symSepName] `mappend` "F"
dummySymbol = dummyName

intSymbol :: (Show a) => Symbol -> a -> Symbol
intSymbol x i       = x `mappend` symbol ('_' : show i)

tempSymbol, existSymbol :: Symbol -> Integer -> Symbol
tempSymbol  prefix = intSymbol (tempPrefix  `mappend` prefix)
existSymbol prefix = intSymbol (existPrefix `mappend` prefix)

renameSymbol :: Symbol -> Int -> Symbol
renameSymbol prefix = intSymbol (renamePrefix `mappend` prefix)

tempPrefix, anfPrefix, existPrefix, renamePrefix, litPrefix :: Symbol
tempPrefix   = "lq_tmp_"
anfPrefix    = "lq_anf_"
existPrefix  = "lq_ext_"
renamePrefix = "lq_rnm_"
litPrefix    = "lit$"

nonSymbol :: Symbol
nonSymbol = ""

isNonSymbol :: Symbol -> Bool
isNonSymbol = (== nonSymbol)

------------------------------------------------------------------------------
-- | Values that can be viewed as Symbols
------------------------------------------------------------------------------

class Symbolic a where
  symbol :: a -> Symbol

instance Symbolic T.Text where
  symbol = toSymbol

instance Symbolic String where
  symbol = symbol . T.pack

-- instance Symbolic InternedText where
--   symbol = S

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
tupConName   = "Tuple"
propConName  = "Prop"
hpropConName = "HProp"
strConName   = "Str"
vvName       = "VV"

symSepName   :: Char
symSepName   = '#' -- Do not ever change this

nilName      = "nil"    :: Symbol
consName     = "cons"   :: Symbol

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
        , nilName
        , consName
        ]
