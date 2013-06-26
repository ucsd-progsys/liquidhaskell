module Fixme where

data F a = F a
{-@ data F a = F (x::{v:a | v = y }) @-}



