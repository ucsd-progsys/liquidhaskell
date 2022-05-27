module Mr00 () where

import Language.Haskell.Liquid.Prelude 
import Data.Map hiding (filter, map, foldl)

baz (v:vs) _ = crash False 
baz []     _ = crash False

mymap = Data.Map.fromList [('a', [1])]

-- Why is this safe
coll = Data.Map.foldr baz 0 
prop_safe = coll mymap 

-- Oddly, this is unsafe
-- prop_unsafe = Data.Map.foldr baz 0 mymap
