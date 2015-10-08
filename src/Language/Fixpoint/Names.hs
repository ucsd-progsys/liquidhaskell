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
  , symbolText
  , symbolString

  -- Predicates
  , isPrefixOfSym
  , isSuffixOfSym
  , isNonSymbol
  , isNontrivialVV

  -- * Destructors
  -- , stripParensSym
  -- , stripParens
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
  , renameSymbol

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

import           System.IO.Unsafe            (unsafePerformIO)
import           Control.DeepSeq             (NFData (..))
import           Control.Arrow               (second)
import           Control.Monad               ((>=>))
import           Data.IORef
-- import           Data.Char                   (isAlpha, chr, ord)
import           Data.Generics               (Data)
import           Data.Hashable               (Hashable (..))
import qualified Data.HashSet                as S
import qualified Data.HashMap.Strict         as M
import           Data.Interned               (intern, unintern)
import           Data.Interned.Internal.Text
import           Data.Maybe                  (fromMaybe)
import           Data.String                 (IsString(..))
import qualified Data.Text                   as T
import           Data.Binary                 (Binary (..))
import           Data.Typeable               (Typeable)
import           GHC.Generics                (Generic)

import           Language.Fixpoint.Misc      (safeLookup, errorstar)
import Debug.Trace

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
  mappend s1 s2 = toSymbol $ mappend s1' s2'
    where
      s1'       = symbolText s1
      s2'       = symbolText s2


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
  get = toSymbol <$> get
  put = put . symbolText

symbolSafeText :: Symbol -> SafeText
symbolSafeText (S s) = unintern s

symbolSafeString :: Symbol -> String
symbolSafeString = T.unpack . symbolSafeText

-- symbolText :: Symbol -> T.Text
-- symbolText x = traceShow msg $ symbolText' x
  -- where
    -- msg            = "SyUnTxt: x = " ++ show (symbolSafeText x)

symbolText :: Symbol -> T.Text
symbolText x
  | Just i <- encId s = memoDecode i
  | otherwise         = s
  where
    s                 = symbolSafeText x

encId :: T.Text -> Maybe Int
encId = fmap t2i . T.stripPrefix encPrefix

t2i :: T.Text -> Int
t2i = read . T.unpack

symbolString :: Symbol -> String
symbolString = T.unpack . symbolText

safeTextSymbol :: SafeText -> Symbol
safeTextSymbol = S . intern

---------------------------------------------------------------------------
-- | Converting Strings To Fixpoint ---------------------------------------
---------------------------------------------------------------------------

-- INVARIANT: All strings *must* be built from here
toSymbol :: T.Text -> Symbol
toSymbol = safeTextSymbol . encode


-- encode 'abs#45' == 'enc$7' where 7 |-> 'abs#45'

encode :: T.Text -> SafeText
encode t
  | isSafeText t   = t
  | otherwise      = safeCat encPrefix (i2t i)
  where
    i              = memoEncode t
    i2t            = T.pack . show

encPrefix :: SafeText
encPrefix = "enc$"

safeCat :: SafeText -> SafeText -> SafeText
safeCat = mappend

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


safeChars :: [Char]
safeChars = ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ ['_', '.'  ]

-- | RJ: We allow the extra 'unsafeChars' to allow parsing encoded symbols.
--   e.g. the raw string "This#is%$inval!d" may get encoded as "enc%12"
--   and serialized as such in the fq/bfq file. We want to allow the parser
--   to then be able to read the above back in.

symChars :: S.HashSet Char
symChars =  S.fromList $ ['%', '#', '$'] ++ safeChars

okSymChars :: S.HashSet Char
okSymChars = S.fromList safeChars

isPrefixOfSym :: Symbol -> Symbol -> Bool
isPrefixOfSym (symbolText -> p) (symbolText -> x) = p `T.isPrefixOf` x

isSuffixOfSym :: Symbol -> Symbol -> Bool
isSuffixOfSym (symbolText -> p) (symbolText -> x) = p `T.isSuffixOf` x

takeWhileSym :: (Char -> Bool) -> Symbol -> Symbol
takeWhileSym p (symbolText -> t) = symbol $ T.takeWhile p t

headSym :: Symbol -> Char
headSym (symbolText -> t) = T.head t

consSym :: Char -> Symbol -> Symbol
consSym c (symbolText -> s) = symbol $ T.cons c s

unconsSym :: Symbol -> Maybe (Char, Symbol)
unconsSym (symbolText -> s) = second symbol <$> T.uncons s

singletonSym :: Char -> Symbol -- Yuck
singletonSym = (`consSym` "")

lengthSym :: Symbol -> Int
lengthSym (symbolText -> t) = T.length t

dropSym :: Int -> Symbol -> Symbol
dropSym n (symbolText -> t) = symbol $ T.drop n t

stripPrefix :: Symbol -> Symbol -> Maybe Symbol
stripPrefix p x = symbol <$> T.stripPrefix (symbolText p) (symbolText x)



-- stripParens :: T.Text -> T.Text
-- stripParens t = fromMaybe t (strip t)
--  where
--    strip = T.stripPrefix "(" >=> T.stripSuffix ")"

-- stripParensSym :: Symbol -> Symbol
-- stripParensSym (symbolText -> t) = symbol $ stripParens t

---------------------------------------------------------------------

vv                  :: Maybe Integer -> Symbol
vv (Just i)         = symbol $ symbolSafeText vvName `T.snoc` symSepName `mappend` T.pack (show i) --  S (vvName ++ [symSepName] ++ show i)
vv Nothing          = vvName

isNontrivialVV      = not . (vv Nothing ==)

vvCon, dummySymbol :: Symbol
vvCon       = vvName `mappend` symbol [symSepName] `mappend` "F"
dummySymbol = dummyName

intSymbol :: (Show a) => Symbol -> a -> Symbol
intSymbol x i       = x `mappend` symbol ('_' : show i)

tempSymbol :: Symbol -> Integer -> Symbol
tempSymbol prefix = intSymbol (tempPrefix `mappend` prefix)

renameSymbol :: Symbol -> Int -> Symbol
renameSymbol prefix = intSymbol (renamePrefix `mappend` prefix)

tempPrefix, anfPrefix, renamePrefix, litPrefix :: Symbol
tempPrefix   = "lq_tmp_"
anfPrefix    = "lq_anf_"
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

nilName, consName, size32Name, size64Name, bitVecName, bvOrName, bvAndName :: Symbol
nilName      = "nil"
consName     = "cons"
size32Name   = "Size32"
size64Name   = "Size64"
bitVecName   = "BitVec"
bvOrName     = "bvor"
bvAndName    = "bvAnd"

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

-------------------------------------------------------------------------------
-- | Memoized Decoding
-------------------------------------------------------------------------------

{-# NOINLINE symbolMemo #-}
symbolMemo :: IORef (M.HashMap Int T.Text)
symbolMemo = unsafePerformIO (newIORef M.empty)

{-# NOINLINE memoEncode #-}
memoEncode :: T.Text -> Int
memoEncode t = unsafePerformIO $
                 atomicModifyIORef symbolMemo $ \m ->
                    (M.insert i t m, i)
  where
    i        = internedTextId $ intern t

{-# NOINLINE memoDecode #-}
memoDecode :: Int -> T.Text
memoDecode i = unsafePerformIO $
                 safeLookup msg i <$> readIORef symbolMemo
               where
                 msg = "Symbol Decode Error: " ++ show i
