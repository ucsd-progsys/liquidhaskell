-- TAG: names 

module Vector1 where

-- import Language.Haskell.Liquid.Prelude

-- import Data.Vector hiding (map, concat, zipWith, filter, foldl, foldr, (++))
import qualified Data.Vector as V 

{-@ prop :: [TT] @-}
prop      = [prop0, prop1, prop2, prop3, prop4]
  where
    xs    = [1,2,3,4] :: [Int]
    vs    = V.fromList xs
    x     = Prelude.head xs
    n     = Prelude.length xs
    prop0 = (x >= 0)
    prop1 = (n > 0)
    prop2 = (V.length vs > 0)
    prop3 = (V.length vs > 3)
    prop4 = ((vs V.! 0 + vs V.! 1 + vs V.! 2 + vs V.! 3) > 0)
