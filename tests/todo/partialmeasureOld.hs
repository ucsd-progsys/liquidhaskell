module Head where

{-@ measure hd :: [a] -> a
    hd (x:xs) = x
  @-}

-- Strengthened constructors
--   data [a] where
--     []  :: [a]    -- as before
--     (:) :: x:a -> xs:[a] -> {v:[a] | hd v = x}

{-@ cons :: x:a -> _ -> {v:[a] | hd v = x} @-}
cons x xs = x : xs

{-@ test :: {v:_ | hd v = 0} @-}
test     :: [Int]
test     =  cons 0 [1,2,3,4]




