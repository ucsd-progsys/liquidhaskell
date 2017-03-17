foo :: Int 
foo = 1 

bar :: Int 
bar = 1 
{-@ LIQUID "--higher-order" @-}
{-@ unsound :: () -> {v:Bool |  foo == bar } @-}
unsound :: () -> Bool
unsound _ = foo == bar 