{-@ LIQUID "--expect-any-error" @-}
module CastedTotality where

import Language.Haskell.Liquid.Prelude

main = show x
  where Just x = (Nothing :: Maybe Int)


main0 = do 
     let Just x = Nothing 
     print (x :: Int)

