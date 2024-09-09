{-@ LIQUID "--reflection"      @-}

module OpaqueRefl04 where

{-@ reflect keepEvens @-}
keepEvens :: [Int] -> [Int]
keepEvens = filter even
