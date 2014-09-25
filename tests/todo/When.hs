module When (foo, fooOk) where

{-@ assume div :: x:_ -> y:{_ | y /= 0} -> _ @-}

{- when :: b:Bool -> {v:_ | ???} -> _ -}
when b x = if b then x else return ()


foo :: Int -> IO ()
foo x = when (x > 0) $ print (1 `div` x)

{-@ whenT :: b:_ -> ({v:_ | Prop b} -> _) -> _ @-}
whenT :: Bool -> (() -> IO ()) -> IO ()
whenT b k = if b then k () else return ()

fooOk :: Int -> IO ()
fooOk x = whenT (x > 0) $ \() -> print (1 `div` x)
