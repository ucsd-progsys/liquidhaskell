module PositivityCheck where

data Good1 a = Nil | Cons a (Good1 a)
data Good2 a = Yes ((Good2 a -> Int) -> Int)

data GoodRec1 a = YesRec1 (GoodRec2 a -> Int)
data GoodRec2 a = YesRec2 (GoodRec1 a -> Int)

