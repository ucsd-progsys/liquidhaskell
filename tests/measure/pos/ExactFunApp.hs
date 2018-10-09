-- TAG: reflect
-- TAG: measure
{-@ LIQUID "--no-totality"     @-}
{-@ LIQUID "--reflection"      @-}

module ListFunctors where

bar :: Maybe (a -> a) -> a -> a
{-@ bar :: xy:Maybe (a -> a) -> z: a -> {v: a | v == from_Just xy z} @-}
bar xink z = from_Just xink z


-- TODO-REBARE: this used to work with `measure` as well, but was broken by REBARE;
-- it can be fixed by adding `measure` vars to `gsReflects` and hence, the `aenv` 
-- used by constraint-generation (which tickles some singleton-heuristic) but 
-- currently that breaks a few measure tests. So, for now, just reverting this 
-- to `reflect` (as it does not affect the reflection or PLE benchmarks.)

{-@ reflect from_Just @-}
from_Just :: Maybe a -> a
from_Just (Just x) = x