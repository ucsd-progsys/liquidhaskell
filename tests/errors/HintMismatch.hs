{-@ LIQUID "--expect-error-containing=HINT: Use the hole" @-}

{-# LANGUAGE DataKinds #-}

module HintMismatch where

newtype Offset struct member = Offset { unOffset :: Int }

type OffsetN t = Offset (t 'Nothing)

foo = Nothing 

{-@ bar :: t 'Nothing @-}
bar :: t 'Nothing
bar = undefined 
