module MaskError where

{-@ assume error :: String -> a @-}

foo :: Int -> Int 
foo _ = error "oh no"
