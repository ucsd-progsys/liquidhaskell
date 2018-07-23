module Inc01 where 

{-@ inc :: GHC.Types.Int -> {v:GHC.Types.Int | v >= 0} @-}
inc :: Int -> Int 
inc x = one -- 1


{-@ one :: {v:GHC.Types.Int | v >= 0} @-}
one :: Int 
one = undefined
