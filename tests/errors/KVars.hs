{-@ LIQUID "--expect-error-containing=v < 0" @-}
-- | Tests that KVar solutions show in error messages
module KVars where


{-@ intId :: forall <p :: Int -> Bool> . Int<p> -> Int<p> @-}
intId :: Int -> Int
intId x = x

{-@ test :: {x:Int | x < 0} -> {v:Int | v > 0} @-}
test :: Int -> Int
test x = intId x
