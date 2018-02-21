module SingletonLists where

{-@ LIQUID "--higherorder" @-}

{-@ infix : @-}

empList :: ([a] -> a) -> ()
{-@ empList :: f:([a] -> a) -> {f [] == f []} @-}
empList _ = ()


singletonList :: ([a] -> a) -> a -> ()
{-@ singletonList :: f:([a] -> a) -> x:a -> {f [x] == f [x]} @-}
singletonList _ _ = ()

singletonListC :: ([a] -> a) -> a -> ()
{-@ singletonListC :: f:([a] -> a) -> x:a -> {f (x:[]) == f [x]} @-}
singletonListC _ _ = ()

