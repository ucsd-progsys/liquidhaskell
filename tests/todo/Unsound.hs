module Unsound where

{-@ assume magic :: {v:() | false} @-}
magic :: ()
magic = undefined 

bar = head []