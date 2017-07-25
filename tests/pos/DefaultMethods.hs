module DefaultMethods where

class Bad t where
  mkBad :: t -> String

  mkBad2 :: Int -> t -> String
  mkBad2 _ = mkBad

instance Bad Char where
  mkBad = show

instance Bad Int where
  mkBad = show
