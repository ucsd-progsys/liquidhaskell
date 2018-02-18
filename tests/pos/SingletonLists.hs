module SingletonLists where

{-@ LIQUID "--higherorder" @-}

empList :: ([a] -> a) -> ()
{-@ empList :: f:([a] -> a) -> {f [] == f []} @-}
empList _ = ()


singletonList :: ([a] -> a) -> a -> ()
{-@ singletonList :: f:([a] -> a) -> x:a -> {f [x] == f [x]} @-}
singletonList _ _ = ()