module ImportedNumericInstances where

import System.Posix.Types (Fd)
-- Fd is a data type that is imported to be a num instance

{- embed System.Posix.Types.Fd as int @-}

extractSocketFd0 :: Maybe [a] -> Fd
extractSocketFd0 = 
 maybe 0 (fromIntegral . getFoo)



{-@ getFoo :: {v:[a] | 0 <= len v}  -> Int @-} 
getFoo :: [a] -> Int 
getFoo = undefined 
