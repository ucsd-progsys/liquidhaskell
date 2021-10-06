{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.List.NonEmpty where

import           Prelude                 hiding ( foldr
                                                , head
                                                , tail
                                                )

import           Data.List

{-@ data NonEmpty a = NonEmpty {neh::a, net:: (List a)} @-}
data NonEmpty a = NonEmpty a (List a)

{-@ reflect head' @-}
head' :: NonEmpty a -> a
head' (NonEmpty a _) = a

{-@ reflect tail' @-}
tail' :: NonEmpty a -> List a
tail' (NonEmpty _ t) = t
