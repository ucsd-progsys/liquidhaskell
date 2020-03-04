
module ReturnStrata00 where

bar :: IO () 
bar = if True then return () else undefined
