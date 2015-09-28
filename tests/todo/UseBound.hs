module UseBound where

import ImportBound

-- This crashes because the type of `by` has a bound Chain that
-- is unknown at import

myby = by
