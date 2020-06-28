module T338 where

-- available as tests/todo/boolparse.hs

-- It would be nice to parse the below:

{-@ type BoolP P = {v:Bool | v <=> P} @-}

-- The below works fine (obviously)
{- type BoolP P = {v:Bool | true } @-}

-- We can then write things like:

{-@ inline gt @-}
gt :: Int -> Int -> Bool
gt x y = x > y

{-@ isNat :: x:Int -> BoolP {gt x 0} @-}
isNat :: Int -> Bool
isNat x = x > 0
