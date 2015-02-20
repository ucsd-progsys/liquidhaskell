module Fixme where


import qualified Data.Set


{-@ foo :: x:[a]  
          -> {v:[a] | Set_sub (listElts x) (listElts v)}
  @-}

foo = catMaybes . map bar 
  where
    catMaybes [] = []
    catMaybes (Nothing:xs) = catMaybes xs
    catMaybes (Just x : xs) = x:catMaybes xs

bar :: a -> Maybe a
{-@ bar :: x:a -> Maybe {v:a | v = x } @-}
bar x = if prop x then Nothing else Just x

{-@ prop :: a -> Bool @-}
prop :: a -> Bool
prop = undefined

