{-# LANGUAGE UnicodeSyntax #-}

module UnicodeSyntax where

{-@ id10 :: x:Int -> {v:Int | v = x} @-}
id10 :: Int -> Int
id10 x = x

{-@ id11 :: x:Int -> {v:Int | v = x} @-}
id11 ∷ Int → Int
id11 x = x

{-@ id20 ∷ x:Int → {v:Int | v = x} @-}
id20 :: Int -> Int
id20 x = x

{-@ id21 ∷ x:Int → {v:Int | v = x} @-}
id21 ∷ Int → Int
id21 x = x

{-@ id3 :: x:Int → {v:Int | v = x} @-}
id3 :: Int → Int
id3 x = x

{-@ id4 ∷ x:Int -> {v:Int | v = x} @-}
id4 ∷ Int -> Int
id4 x = x
