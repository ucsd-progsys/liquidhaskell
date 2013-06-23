module Cont where

cont :: (() -> Int) -> Int
cont f = f () 

{-@ funkyId :: x:Int -> {v:Int | v = x} @-}
funkyId :: Int -> Int
funkyId n = cont (\_ -> n)

