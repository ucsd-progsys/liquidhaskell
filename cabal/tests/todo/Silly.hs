
import LPrelude

class Foo a where
  fstF :: a -> a -> a
  sndF :: a -> a -> a

instance Foo Int where
  fstF x y = x
  sndF x y = y

silly ::  (Foo a) => a -> a -> a
silly x y = fstF x y

sillyI ::  Int -> Int -> Int 
sillyI x y = fstF x y

x0   = sillyI 2 4

main = do putStrLn $ "sillyI 2 4 = " ++ show x0 
