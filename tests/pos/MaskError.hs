module MaskError where 

{-@ assume Prelude.error :: String -> a @-}

foo :: Int -> Int 
foo _ = error "oh no"
