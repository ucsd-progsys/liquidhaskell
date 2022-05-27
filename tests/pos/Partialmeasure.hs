{-@ LIQUID "--no-totality" @-}

module Partialmeasure where

-- Note: `partialmeasureOld.hs` works fine 

{-@ cons :: x:a -> _ -> {v:[a] | hd v = x} @-}
cons x xs = x : xs

{-@ test :: {v:_ | hd v = 0} @-}
test :: [Int]
test =  cons 0 [1,2,3,4]

{-@ measure hd @-}
hd       :: [a] -> a
hd (x:_) = x


-- Instead of rejecting, can we just default to "un-refined" constructors?

-- Strengthened constructors
--   data [a] where
--     []  :: [a]    -- as before
--     (:) :: x:a -> xs:[a] -> {v:[a] | hd v = x}




