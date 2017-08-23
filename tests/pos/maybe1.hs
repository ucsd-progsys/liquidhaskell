{-@ LIQUID "--no-totality" @-}

module Test (isJustS, fromJustS) where

data MaybeS a = NothingS | JustS !a

{-@ measure isJustS @-}
isJustS :: MaybeS a -> Bool
isJustS (JustS x)  = True
isJustS (NothingS) = False

{-@ measure fromJustS @-}
fromJustS :: MaybeS a -> a
fromJustS (JustS x) = x

{-@ type OList a = [a]<{\fld v -> (v >= fld)}> @-}

{-@ filterGt :: (Ord a) => x:MaybeS a -> OList a -> OList {v:a | isJustS x => fromJustS x <= v } @-}

filterGt ::  Ord a => MaybeS a -> [a] -> [a]
filterGt NothingS  xs = xs
filterGt (JustS x) xs = foo' x xs
  where foo' y []     = []
        foo' y (x:xs) = case compare y x of
                          GT -> foo' y xs
                          LT -> x:xs
                          EQ -> xs
