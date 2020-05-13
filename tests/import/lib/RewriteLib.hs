{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-@ infix ++ @-}

module RewriteLib where
import Prelude hiding ((++))

{-@ reflect ++ @-}
(++)::[a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ys)

{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a]
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc [] _ _       = ()
assoc (_:xs) ys zs = assoc xs ys zs
