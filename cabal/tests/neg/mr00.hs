module MapReduce where

import Language.Haskell.Liquid.Prelude
import qualified Data.Map as M

baz (v:vs) _ = crash False 
baz []     _ = crash False

mymap = M.fromList [('a', [1])]

-- Why is this safe
coll = M.fold baz 0 
prop_safe = coll mymap 

-- Oddly, this is unsafe
-- prop_unsafe = M.foldr baz 0 mymap
