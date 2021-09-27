{-# LANGUAGE OverloadedStrings    #-}

-- | Wrapper around `Data.Text.Builder` that exports some useful combinators

module Language.Fixpoint.Utils.Builder
  ( Builder
  , fromLazyText
  , fromString
  , fromText
  , toLazyText
  , parens
  , (<+>)
  , parenSeqs
  , seqs
  , key
  , key2
  , key3
  , bShow
  , bFloat
  , bb
  , lbb
  , blt
  ) where

import           Data.String
import qualified Data.Text.Lazy.Builder as B
import qualified Data.Text.Lazy         as LT
import qualified Data.Text              as T
import qualified Data.List              as L
import qualified Numeric

-- | Offers efficient concatenation, no matter the associativity
data Builder
  = Node Builder Builder
  | Leaf B.Builder

instance Eq Builder where
  b0 == b1 = toLazyText b0 == toLazyText b1

instance IsString Builder where
  fromString = Leaf . fromString

instance Semigroup Builder where
  (<>) = Node

instance Monoid Builder where
  mempty = Leaf mempty

toLazyText :: Builder -> LT.Text
toLazyText = B.toLazyText . go mempty
  where
    go tl (Leaf b) = b <> tl
    go tl (Node t0 t1) = go (go tl t1) t0

fromLazyText :: LT.Text -> Builder
fromLazyText = Leaf . B.fromLazyText

fromText :: T.Text -> Builder
fromText = Leaf . B.fromText

parens :: Builder -> Builder
parens b = "(" <>  b <> ")"

(<+>) :: Builder -> Builder -> Builder
x <+> y = x <> " " <> y

parenSeqs :: [Builder] -> Builder
parenSeqs = parens . seqs

key :: Builder -> Builder -> Builder
key k b = parenSeqs [k, b]

key2 :: Builder -> Builder -> Builder -> Builder
key2 k b1 b2 = parenSeqs [k, b1, b2]

key3 :: Builder -> Builder -> Builder -> Builder ->  Builder
key3 k b1 b2 b3 = parenSeqs [k, b1, b2, b3]

seqs :: [Builder] -> Builder
seqs = foldr (<>) mempty . L.intersperse " "

bShow :: Show a => a -> Builder
bShow = fromString . show

bFloat :: RealFloat a => a -> Builder
bFloat d = fromString (Numeric.showFFloat Nothing d "")

bb :: LT.Text -> Builder
bb = fromLazyText

lbb :: T.Text -> Builder
lbb = bb . LT.fromStrict

blt :: Builder -> LT.Text
blt = toLazyText

