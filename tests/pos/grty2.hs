module Test () where

{-@ foo :: {vv:[{v:[a]|((len v) = 1)}]|((len vv)= 1)} -> [[a]] @-}
foo [[x]] = [[x]]



