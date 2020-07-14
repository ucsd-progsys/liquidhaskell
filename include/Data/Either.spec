module spec Data.Either where

measure isLeft :: Data.Either.Either a b -> Bool
  isLeft (Left x)  = true
  isLeft (Right x) = false
