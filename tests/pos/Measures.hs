module Measures where

{-@ data Wrapper a <p :: a -> Prop, r :: a -> a -> Prop > 
    = Wrap (rgref_ref :: a<p>) @-}
data Wrapper a = Wrap (a)

-- Two measures
{-@ measure fwdextends :: Int -> Int -> Prop @-}
{-@ measure actionP :: Int -> Prop @-}

{-@ data Wrapper2  = Wrapper2 (unwrapper :: (Wrapper<{\x -> (true)},{\x y -> (fwdextends y x)}> Int )) @-}
{- data Wrapper2  = Wrapper2 (unwrapper :: (Wrapper<{\x -> (actionP x)},{\x y -> (true)}> Int )) @-}
data Wrapper2  = Wrapper2 (Wrapper (Int) )


