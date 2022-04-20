{-@ LIQUID "--reflection" @-}


module ReflectLam where



{-@ reflect bar @-}
bar :: [Integer]
bar = mymap (\x -> x + 1) [1,2,3]

{-@ reflect mymap @-}
mymap :: (a -> b) -> [a] -> [b]
mymap f [] = [] 
mymap f (x:xs) = f x : mymap f xs 
