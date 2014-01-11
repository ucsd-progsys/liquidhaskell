module Monad () where

goo c = return c

foo = 
  do x <- Just 1
     y <- goo 3
     return $ x + y 
