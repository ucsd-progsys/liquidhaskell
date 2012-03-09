module spec Test where

assume foo :: Int -> Int -> Bool
//assume foo :: x:Int -> y: {v:Int | v = x}-> Bool

