module Box (Box, get, put, emp) where

import Data.Dynamic
import Language.Haskell.Liquid.Prelude


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
get k (Box kvs) = fromJust $ fromDynamic =<< lookup k kvs


-----------------------------------------------------------
-- | Helpers
-----------------------------------------------------------

{-@ fromJust      :: {v: Maybe a | isJust v} -> a @-}
fromJust (Just x) = x
fromJust Nothing  = safeError "nein"

{-@ safeError :: {v:_ | false} -> a @-}
safeError = error
