module When where

import Control.Monad

{-@ assume div :: x:_ -> y:{_ | y /= 0} -> _ @-}

{- when :: b:Bool -> {v:_ | ???} -> _ -}

foo :: Int -> IO ()
foo x = when (x > 0) $ print (1 `div` x)

{-@ assume whenT :: b:Bool -> ({v:() | Prop b} -> IO ()) -> IO () @-}
whenT :: Bool -> (() -> IO ()) -> IO ()
whenT b k = when b $ k ()

fooOk :: Int -> IO ()
fooOk x = whenT (x > 0) $ \() -> print (1 `div` x)
