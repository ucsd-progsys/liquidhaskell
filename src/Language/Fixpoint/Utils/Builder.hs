{-# LANGUAGE OverloadedStrings    #-}

-- | Wrapper around `Data.Text.Builder` that exports some useful combinators

module Language.Fixpoint.Utils.Builder where

import qualified Data.Text.Lazy.Builder as B
import qualified Data.Text.Lazy         as LT

parens :: B.Builder -> B.Builder
parens b = "(" <>  b <> ")"

(<+>) :: B.Builder -> B.Builder -> B.Builder 
x <+> y = x <> " " <> y

parenSeq1s :: [B.Builder] -> B.Builder
parenSeq1s = parens . seq1s

key :: B.Builder -> B.Builder -> B.Builder
key k b = parenSeq1s [k, b]

key2 :: B.Builder -> B.Builder ->  B.Builder -> B.Builder
key2 k b1 b2 = parenSeq1s [k, b1, b2]

seq1s :: [B.Builder] -> B.Builder
seq1s = foldr1 (<+>)

fromShow :: (Show a) => a -> B.Builder
fromShow = B.fromString . show

bb :: LT.Text -> B.Builder
bb = B.fromLazyText

blt :: B.Builder -> LT.Text
blt = B.toLazyText

