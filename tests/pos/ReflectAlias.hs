-- See LH #1086 

{-# LANGUAGE ScopedTypeVariables #-}

module Bob where

type Val = Int

{-@ reflect poo @-}
poo :: Int -> Int
poo y = (\(x :: Val) -> x + 1) y
