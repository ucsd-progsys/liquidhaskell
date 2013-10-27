module Blank where


{-@ type ListN a N = {v:[a] | (len v) = N} @-}

-- TODO: extend parser to allow expressions, at the very least, 
--       literals as arguments! Currently, the below is rejected by the parser.

{-@ xs :: (ListN Int 2) @-}
xs :: [Int]
xs = [1,2] 
