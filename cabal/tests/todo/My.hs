module My (My (..), emp) where

data My a = Nil | Cons a (My a)

emp :: My Int 
emp = Nil 

