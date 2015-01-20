module Foo where

isEven 0 = True
isEven n = isOdd (n - 1)

isOdd 0 = False
isOdd n = isEven (n - 1)
