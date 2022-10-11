{-@ LIQUID "--no-positivity-check" @-}

module NoPositivityCheck where

data Bad1 a = No11 (Bad1 a -> Int) | No12 (Bad1 a) 
data Bad2 a = No2 (Int -> Bad2 a -> Int)
data Bad3 a = No3 (Bad3 Int -> Int)

data BadRec1 a = NoRec1 (BadRec2 a -> Int)
data BadRec2 a = NoRec2 (BadRec1 a)
