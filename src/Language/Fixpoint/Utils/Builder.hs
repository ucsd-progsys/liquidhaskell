{-# LANGUAGE OverloadedStrings    #-}

-- | Wrapper around `Data.Text.Builder` that exports some useful combinators

module Language.Fixpoint.Utils.Builder where

import qualified Data.Text.Lazy.Builder as B
import qualified Data.Text.Lazy         as LT
import qualified Data.Text              as T
import qualified Data.List              as L
import qualified Numeric 

parens :: B.Builder -> B.Builder
parens b = "(" <>  b <> ")"

(<+>) :: B.Builder -> B.Builder -> B.Builder 
x <+> y = x <> " " <> y

parenSeqs :: [B.Builder] -> B.Builder
parenSeqs = parens . seqs

key :: B.Builder -> B.Builder -> B.Builder
key k b = parenSeqs [k, b]

key2 :: B.Builder -> B.Builder ->  B.Builder -> B.Builder
key2 k b1 b2 = parenSeqs [k, b1, b2]

key3 :: B.Builder -> B.Builder ->  B.Builder -> B.Builder ->  B.Builder
key3 k b1 b2 b3 = parenSeqs [k, b1, b2, b3]

seqs :: [B.Builder] -> B.Builder
seqs = foldr (<>) mempty . L.intersperse " "

bShow :: (Show a) => a -> B.Builder
bShow = B.fromString . show

bFloat :: RealFloat a => a -> B.Builder
bFloat d = B.fromString (Numeric.showFFloat Nothing d "") 

bb :: LT.Text -> B.Builder
bb = B.fromLazyText

lbb :: T.Text -> B.Builder
lbb = bb . LT.fromStrict

blt :: B.Builder -> LT.Text
blt = B.toLazyText

