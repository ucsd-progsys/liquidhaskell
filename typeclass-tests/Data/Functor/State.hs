module Data.Functor.State where

{-@ data State s a = State {runState :: s -> (a,s)} @-}
data State s a = State {runState :: s -> (a,s)}
