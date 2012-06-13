module Vec0 where

<<<<<<< HEAD
import Language.Haskell.Liquid.Prelude
=======
import Language.Haskell.Liquid.Prelude -- hiding (copyList)
>>>>>>> origin/preds

copyList zs = zs

xs    = [1] :: [Int]
ys    = copyList xs
jhala = head ys
prop0 = crash (0 == 1) 
