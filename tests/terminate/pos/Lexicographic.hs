module Lexicographic where

foo012 (x:xs) ys     zs     = 1 + foo012 xs ys zs
foo012 []     (y:ys) zs     = 1 + foo012 [] ys zs
foo012 []     []     (z:zs) = 1 + foo012 [] [] zs
foo012 []     []     []     = 0

foo021 (x:xs) zs     ys     = 1 + foo021 xs zs ys
foo021 []     zs     (y:ys) = 1 + foo021 [] zs ys
foo021 []     (z:zs) []     = 1 + foo021 [] zs []
foo021 []     []     []     = 0

foo102 ys     (x:xs) zs     = 1 + foo102 ys xs zs
foo102 (y:ys) []     zs     = 1 + foo102 ys [] zs
foo102 []     []     (z:zs) = 1 + foo102 [] [] zs
foo102 []     []     []     = 0

foo120 ys     zs     (x:xs) = 1 + foo120 ys zs xs
foo120 (y:ys) zs     []     = 1 + foo120 ys zs []
foo120 []     (z:zs) []     = 1 + foo120 [] zs []
foo120 []     []     []     = 0

foo201 zs     (x:xs) ys     = 1 + foo201 zs xs ys
foo201 zs     []     (y:ys) = 1 + foo201 zs [] ys
foo201 (z:zs) []     []     = 1 + foo201 zs [] []
foo201 []     []     []     = 0

foo210 zs     ys     (x:xs) = 1 + foo210 zs ys xs
foo210 zs     (y:ys) []     = 1 + foo210 zs ys []
foo210 (z:zs) []     []     = 1 + foo210 zs [] []
foo210 []     []     []     = 0
