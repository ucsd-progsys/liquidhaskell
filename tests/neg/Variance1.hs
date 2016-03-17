import Data.Binary


{-@
error :: { x : String | false } -> a
@-}

example :: Get ()
example = do
    _ <- return ()
    error "URK"