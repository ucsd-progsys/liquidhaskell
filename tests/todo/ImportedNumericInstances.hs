module ImportedNumericInstances where

{- embed System.Posix.Types.Fd as int @-}

import System.Posix.Types (Fd)
-- Fd is a data type that is imported to be a num instance

testToFix :: Maybe [a] -> Fd 
testToFix =  maybe 0 (fromIntegral . getFoo)


testOK :: Maybe [a] -> Boo 
testOK =  maybe 0 (fromIntegral . getFoo)

instance Num Boo where
data Boo 

{-@ getFoo :: {v:[a] | 0 <= len v}  -> Int @-} 
getFoo :: [a] -> Int 
getFoo = undefined 
