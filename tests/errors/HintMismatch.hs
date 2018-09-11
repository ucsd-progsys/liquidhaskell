
{-# LANGUAGE DataKinds #-}

newtype Offset struct member = Offset { unOffset :: Int }

type OffsetN t = Offset (t 'Nothing)

foo = Nothing 

{-@ bar :: t 'Nothing @-}
bar :: t 'Nothing
bar = undefined 