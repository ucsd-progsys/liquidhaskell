module Overload where

import Data.Monoid

bar1, bar2 :: List Int

type List a = [a]

{-@ type ListN a N = { v:[a] | len v == N } @-}

{-@ instance Monoid (List a) where
      mempty  :: ListN a 0
      mappend :: xs:[a] -> ys:[a] -> ListN a {len xs + len ys}
      mconcat :: List (List a) -> List a
  @-}

{-@ bar1 :: ListN Int 6 @-}
bar1 = [1,2,3] ++ [4,5,6]

{-@ bar2 :: ListN Int 6 @-}
bar2 = [1,2,3] <> [4,5,6]
