module Rec1 where

import Control.Monad.ST 
import Data.IORef 

import System.IO.Unsafe

-- recursion with references in ocaml
--
-- bar = 
--   let f = ref (fun _ => 0) in 
--   let foo f n = if n > 0 then n-1 else !f n
--   f := (foo f); !f

-- translation to Haskell

f n = unsafePerformIO $ (unsafePerformIO bar) n

bar :: IO (Int -> IO Int)
bar  = do f <- newIORef (\_ -> return 0)
          writeIORef f (foo f)
          readIORef f

foo     :: (IORef (Int -> IO Int)) -> Int -> IO Int
foo f n  | n > 0     = return $ n-1 
         | otherwise = readIORef f >>= \g -> g n
