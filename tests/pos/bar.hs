module Bar where

import Language.Haskell.Liquid.Prelude

prop = let s = (\x -> x + 1)  $ 3 in 
       let s1 = (\x -> x - 1) $ 4 in
       liquidAssertB (s > 3 && s1 < 4) 



let str0 = "len :: forall a. [a] -> GHC.Types.Int"
let str1 = "len ([])     = 0"
let str2 = "len (y:ys)   = 1 + (len ys)"
let str  = intercalate "\n" [str0, str1, str2]

let str = "len :: forall a. [a] -> GHC.Types.Int\nlen ([])     = 0\nlen (y:ys)   = 1 + (len ys)"
let str1 = "GHC.Types.Int\nlen ([])     = 0\nlen (y:ys)   = 1 + (len ys)"

