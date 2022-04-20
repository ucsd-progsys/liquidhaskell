module Vector04 where

-- test that the name `Vector` gets resolved to
--   `Data.Vector.Vector` 
-- and not 
--  `Data.Vector.Generic.Base.Vector`

import Data.Vector 

{-@ foo :: Vector Int -> Int  @-}
foo :: Vector Int -> Int 
foo _ = 1 

main :: IO ()
main = pure ()
