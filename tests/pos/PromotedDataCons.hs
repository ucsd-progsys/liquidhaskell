
{-# LANGUAGE DataKinds #-}

module PromotedDataCons where

newtype Offset struct member = Offset { unOffset :: Int }

type OffsetN t = Offset (t 'Nothing)

foo = Nothing 

{-@ bar :: t _       @-}
bar :: t 'Nothing
bar = undefined 
