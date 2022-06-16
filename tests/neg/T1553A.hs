{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--extensionality" @-}

module T1553A where

{-@ assume extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> { f x == g x }) -> {f == g} @-}
extensionality :: (a -> b) -> (a -> b) -> (a -> ()) -> ()
extensionality _ _ _ = () 


{-@ bar :: f:(a -> b) -> g:(a -> b) -> {f == g} @-}
bar :: (a -> b) -> (a -> b) -> ()
bar f g  = extensionality f g (\_ -> ())
