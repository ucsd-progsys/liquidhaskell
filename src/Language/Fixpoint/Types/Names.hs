{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE BangPatterns               #-}


-- | This module contains Haskell variables representing globally visible names.
--   Rather than have strings floating around the system, all constant names
--   should be defined here, and the (exported) variables should be used and
--   manipulated elsewhere.

module Language.Fixpoint.Types.Names (

  -- * Symbols
    Symbol
  , Symbolic (..)
  , LocSymbol
  , LocText

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
  , isDummy

  -- * Destructors
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
  , kArgPrefix

  -- * Creating Symbols
  , dummySymbol
  , intSymbol
  , tempSymbol
  , renameSymbol
  , kArgSymbol
  , existSymbol

  -- * Hardwired global names
  , dummyName
  , preludeName
  , boolConName
  , funConName
  , listConName
  , listLConName
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
  , mulFuncName
  , divFuncName

) where

import           Control.DeepSeq             (NFData (..))
import           Control.Arrow               (second)
import           Data.Char                   (ord)
import           Data.Generics               (Data)
import           Data.Hashable               (Hashable (..))
import qualified Data.HashSet                as S
import           Data.Interned
import           Data.Interned.Internal.Text
import           Data.String                 (IsString(..))
import qualified Data.Text                   as T
import           Data.Binary                 (Binary (..))
import           Data.Typeable               (Typeable)
import           GHC.Generics                (Generic)

import           Text.PrettyPrint.HughesPJ   (text)
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Spans

---------------------------------------------------------------
-- | Symbols --------------------------------------------------
---------------------------------------------------------------

deriving instance Data     InternedText
deriving instance Typeable InternedText
deriving instance Generic  InternedText

{- type SafeText = {v: T.Text | IsSafe v} @-}
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



data Symbol
  = S { symbolId      :: !Id
      , symbolRaw     :: !T.Text
      , symbolEncoded :: !T.Text
      } deriving (Data, Typeable, Generic)

instance Eq Symbol where
  S i _ _ == S j _ _ = i == j

instance Ord Symbol where
  compare (S i _ _) (S j _ _) = compare i j

instance Interned Symbol where
  type Uninterned Symbol = T.Text
  newtype Description Symbol = DT T.Text deriving (Eq)
  describe = DT
  identify i t = S i t (encode t)
  cache = sCache

instance Uninternable Symbol where
  unintern (S _ t _) = t

instance Hashable (Description Symbol) where
  hashWithSalt s (DT t) = hashWithSalt s t

instance Hashable Symbol where
  hashWithSalt _ (S i _ _) = i

instance NFData Symbol where
  rnf (S {}) = ()

instance Binary Symbol where
  get = textSymbol <$> get
  put = put . symbolText

sCache :: Cache Symbol
sCache = mkCache
{-# NOINLINE sCache #-}

instance IsString Symbol where
  fromString = textSymbol . T.pack

instance Show Symbol where
  show = show . symbolRaw

instance Monoid Symbol where
  mempty        = ""
  mappend s1 s2 = textSymbol $ mappend s1' s2'
    where
      s1'       = symbolText s1
      s2'       = symbolText s2

instance PPrint Symbol where
  pprint = text . symbolString

instance Fixpoint T.Text where
  toFix = text . T.unpack

instance Fixpoint Symbol where
  toFix = toFix . symbolSafeText

---------------------------------------------------------------------------
-- | Located Symbols -----------------------------------------------------
---------------------------------------------------------------------------

type LocSymbol = Located Symbol
type LocText   = Located T.Text

isDummy :: (Symbolic a) => a -> Bool
isDummy a = symbol a == symbol dummyName

instance Symbolic a => Symbolic (Located a) where
  symbol = symbol . val

---------------------------------------------------------------------------
-- | Decoding Symbols -----------------------------------------------------
---------------------------------------------------------------------------

symbolText :: Symbol -> T.Text
symbolText = symbolRaw

symbolString :: Symbol -> String
symbolString = T.unpack . symbolText

symbolSafeText :: Symbol -> SafeText
symbolSafeText = symbolEncoded

symbolSafeString :: Symbol -> String
symbolSafeString = T.unpack . symbolSafeText

---------------------------------------------------------------------------
-- | Encoding Symbols -----------------------------------------------------
---------------------------------------------------------------------------

-- INVARIANT: All strings *must* be built from here

textSymbol :: T.Text -> Symbol
textSymbol = intern

encode :: T.Text -> SafeText
encode t
  | isFixKey t     = T.append "key$" t
  | otherwise      = encodeUnsafe t

isFixKey :: T.Text -> Bool
isFixKey x = S.member x keywords

encodeUnsafe :: T.Text -> T.Text
encodeUnsafe = joinChunks . splitChunks . prefixAlpha

prefixAlpha :: T.Text -> T.Text
prefixAlpha t
  | isAlpha0 t = t
  | otherwise  = T.append "fix$" t

isAlpha0 :: T.Text -> Bool
isAlpha0 t = case T.uncons t of
               Just (c, _) -> S.member c alphaChars
               Nothing     -> False

joinChunks :: (T.Text, [(Char, SafeText)]) -> SafeText
joinChunks (t, [] ) = t
joinChunks (t, cts) = T.concat $ padNull t : (tx <$> cts)
  where
    tx (c, ct)      = mconcat ["$", c2t c, "$", ct]
    c2t             = T.pack . show . ord

padNull :: T.Text -> T.Text
padNull t
  | T.null t  = "z$"
  | otherwise = t

splitChunks :: T.Text -> (T.Text, [(Char, SafeText)])
splitChunks t = (h, go tl)
  where
    (h, tl)   = T.break isUnsafeChar t
    go !ut    = case T.uncons ut of
                  Nothing       -> []
                  Just (c, ut') -> let (ct, utl) = T.break isUnsafeChar ut'
                                   in (c, ct) : go utl

isUnsafeChar :: Char -> Bool
isUnsafeChar = not . (`S.member` okSymChars)


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
                        , "rhs"
                        , "NaN"
                        , "min"
                        , "map"
                        ]

-- | RJ: We allow the extra 'unsafeChars' to allow parsing encoded symbols.
--   e.g. the raw string "This#is%$inval!d" may get encoded as "enc%12"
--   and serialized as such in the fq/bfq file. We want to allow the parser
--   to then be able to read the above back in.

alphaChars :: S.HashSet Char
alphaChars = S.fromList $ ['a' .. 'z'] ++ ['A' .. 'Z']

numChars :: S.HashSet Char
numChars = S.fromList ['0' .. '9']

safeChars :: S.HashSet Char
safeChars = alphaChars `mappend`
            numChars   `mappend`
            S.fromList ['_', '.'  ]

symChars :: S.HashSet Char
symChars =  safeChars `mappend`
            S.fromList ['%', '#', '$']

okSymChars :: S.HashSet Char
okSymChars = safeChars

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

---------------------------------------------------------------------

vv                  :: Maybe Integer -> Symbol
vv (Just i)         = symbol $ symbolSafeText vvName `T.snoc` symSepName `mappend` T.pack (show i)
vv Nothing          = vvName

isNontrivialVV      :: Symbol -> Bool
isNontrivialVV      = not . (vv Nothing ==)

vvCon, dummySymbol :: Symbol
vvCon       = vvName `mappend` symbol [symSepName] `mappend` "F"
dummySymbol = dummyName

intSymbol :: (Show a) => Symbol -> a -> Symbol
intSymbol x i = x `mappend` symbol ('#' : show i)

tempSymbol :: Symbol -> Integer -> Symbol
tempSymbol prefix = intSymbol (tempPrefix `mappend` prefix)

renameSymbol :: Symbol -> Int -> Symbol
renameSymbol prefix = intSymbol (renamePrefix `mappend` prefix)

kArgSymbol :: Symbol -> Symbol
kArgSymbol x = kArgPrefix `mappend` x

existSymbol :: Symbol -> Integer -> Symbol
existSymbol prefix = intSymbol (existPrefix `mappend` prefix)

tempPrefix, anfPrefix, renamePrefix, litPrefix, kArgPrefix, existPrefix :: Symbol
tempPrefix   = "lq_tmp$"
anfPrefix    = "lq_anf$"
renamePrefix = "lq_rnm$"
litPrefix    = "lit$"
kArgPrefix   = "lq_karg$"
existPrefix  = "lq_ext$"




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
  symbol = textSymbol

instance Symbolic String where
  symbol = symbol . T.pack

instance Symbolic Symbol where
  symbol = id

----------------------------------------------------------------------------
--------------- Global Name Definitions ------------------------------------
----------------------------------------------------------------------------

preludeName, dummyName, boolConName, funConName :: Symbol
preludeName  = "Prelude"
dummyName    = "LIQUID$dummy"
boolConName  = "Bool"
funConName   = "->"

listConName, listLConName, tupConName, propConName, hpropConName, strConName, vvName :: Symbol
listConName  = "[]"
listLConName = "List"
tupConName   = "Tuple"
propConName  = "Prop"
hpropConName = "HProp"
strConName   = "Str"
vvName       = "VV"

symSepName   :: Char
symSepName   = '#' -- DO NOT EVER CHANGE THIS

nilName, consName, size32Name, size64Name, bitVecName, bvOrName, bvAndName :: Symbol
nilName      = "nil"
consName     = "cons"
size32Name   = "Size32"
size64Name   = "Size64"
bitVecName   = "BitVec"
bvOrName     = "bvor"
bvAndName    = "bvAnd"

mulFuncName, divFuncName :: Symbol
mulFuncName  = "Z3_OP_MUL"
divFuncName  = "Z3_OP_DIV"

prims :: [Symbol]
prims = [ propConName
        , hpropConName
        , vvName
        , "Pred"
        , "List"
        , "[]"
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

{-
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

-}
