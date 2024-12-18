-- | Tests that when names overlap, the local one is exported.
--
-- In this case, measure @foo@ is defined in both "MeasureOverlapB" and
-- "MeasureOverlapA". Both definitions are in scope in "MeasureOverlapB",
-- but "MeasureOverlapB" only exports its local @foo@ measure.
--
module MeasureOverlapC where

import MeasureOverlapB

{-@ lemma :: { foo False } @-}
lemma :: ()
lemma = ()
