data I1 = I1 Int -- deriving (Eq, Show)
data I2 = I2 Int -- deriving (Eq, Show)

class MyO a where
  le :: a -> a -> Bool

instance MyO a => MyO [a] where
  le [] []       = True
  le (x:_) (y:_) = le x y
  le _ _         = False

instance MyO I1 where
  le (I1 i) (I1 i') = i <= i'

instance MyO I2 where
  le (I2 i) (I2 i') = i' <= i

order ::  (MyO a) => a -> a -> (a, a)
order x y | le x y    = (x, y)
		  | otherwise = (y, x) 

{-# NOINLINE orders #-}  
orders xs ys = order xs ys

checkOrd ::  (MyO a) => (a, a) -> Bool
checkOrd (x, y) = le x y

r0 = checkOrd $ order (I1 1)    (I1 3)
r1 = checkOrd $ order (I2 1)    (I2 3) 
r2 = checkOrd $ order [(I1 1)] [(I1 3)]
r3 = checkOrd $ order [(I2 1)] [(I2 3)]

main = putStrLn $ show [r0,r1,r2,r3]
