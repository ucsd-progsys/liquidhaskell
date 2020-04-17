module RewriteLib where

{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a]
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc [] _ _       = ()
assoc (_:xs) ys zs = assoc xs ys zs
