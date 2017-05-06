{-@ LIQUID "--no-termination" @-}

module TestRec where

import Prelude hiding (foldl)

data L a = N | C { hd :: a
                 , tl :: L a }

{-@ data L [llen] a = N | C { hd :: a
                            , tl :: L a }
  @-}


{-@ invariant {v:L a | 0 <= llen v} @-}

{-@ measure llen @-}
llen :: L a -> Int
llen N        = 0
llen (C x xs) = 1 + llen xs

reverse :: L a -> L a
reverse xs = go N xs
  where 
    {-@ go :: acc:_ -> xs:_ -> _ / [llen xs] @-}
    go :: L a -> L a -> L a 
    go acc N        = acc
    go acc (C x xs) = go (C x acc) xs

mapL f N = N
mapL f (C x xs) = C (f x) (mapL f xs)


