{-# LANGUAGE OverloadedStrings    #-}

-- | Wrapper around `Data.Text.Builder` that exports some useful combinators

module Language.Fixpoint.Utils.Builder where

import qualified Data.Text.Lazy.Builder as Builder

parens :: Builder.Builder -> Builder.Builder
parens b = "(" <>  b <> ")"

(<+>) :: Builder.Builder -> Builder.Builder -> Builder.Builder 
x <+> y = x <> " " <> y

parenSeq1s :: [Builder.Builder] -> Builder.Builder
parenSeq1s = parens . seq1s

key :: Builder.Builder -> Builder.Builder -> Builder.Builder
key k b = parenSeq1s [k, b]

seq1s :: [Builder.Builder] -> Builder.Builder
seq1s = foldr1 (<+>)

fromShow :: (Show a) => a -> Builder.Builder
fromShow = Builder.fromString . show