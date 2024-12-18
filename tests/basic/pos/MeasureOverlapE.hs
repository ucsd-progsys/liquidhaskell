-- | Tests that when names overlap, the one from the highest module
-- lexicographically is exported.
--
-- In this case, measure @foo@ is defined in both "MeasureOverlapB" and
-- "MeasureOverlapA". Both definitions are in scope in "MeasureOverlapD",
-- but "MeasureOverlapD" only reexports @foo@ from "MeasureOverlapB".
--
module MeasureOverlapE where

import MeasureOverlapD

{-@ lemma :: { foo False } @-}
lemma :: ()
lemma = ()
