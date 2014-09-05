module Box (Box, get, put, emp) where

import Data.Dynamic


-----------------------------------------------------------
type Key    = Int 
newtype Box = Box [(Key, Dynamic)]

-----------------------------------------------------------
emp :: Box
-----------------------------------------------------------
emp = Box []


-----------------------------------------------------------
put :: (Typeable v) => Key -> v -> Box -> Box
-----------------------------------------------------------
put k v (Box kvs) = Box ((k, toDyn v) : kvs) 


-----------------------------------------------------------
get :: (Typeable v) => Key -> Box -> v 
-----------------------------------------------------------
get k (Box kvs) = fromJust k $ fromDynamic =<< lookup k kvs


-----------------------------------------------------------
-- | Helpers
-----------------------------------------------------------

{-@ fromJust :: Key -> {v: Maybe a | isJust v} -> a @-}
fromJust     :: Key -> Maybe a -> a
fromJust _ (Just x) = x
fromJust k Nothing  = safeError $ "Error on key: " ++ show k

{-@ safeError :: {v:_ | false} -> a @-}
safeError = error

-----------------------------------------------------------
-- | Unit Test 
-----------------------------------------------------------

b0 :: Box
b0 = put 0 "Apple"
   $ put 1 (4.5 :: Double)
   $ put 2 ([1,2,3] :: [Int])
   $ emp

okFruit  :: String
okFruit  = get 0 b0

badFruit :: String
badFruit = get 1 b0

okPi     :: Double
okPi     = get 1 b0

badPi    :: Double
badPi    = get 0 b0
