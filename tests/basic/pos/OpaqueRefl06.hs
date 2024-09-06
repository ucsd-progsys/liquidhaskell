-- Checking the opaque-reflection pragma

{-@ LIQUID "--reflection" @-}

module OpaqueRefl06 where

{-@ opaque-reflect lookup @-}
{-@ smartInsert :: k:String -> v:Int -> l:[(String, Int)] -> {res : [(String, Int)] | lookup k l == Just v || head res == (k , v)} @-}
smartInsert :: String -> Int -> [(String, Int)] -> [(String, Int)]
smartInsert k v l
  | lookup k l == Just v = l
  | otherwise = (k, v) : l