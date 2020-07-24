module ReWrite where 

{-@ LIQUID "--max-rw-ordering-constraints=1" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix ++ @-}

import Prelude hiding ((++))


{-@ rewriteWith assoc2 [assoc] @-} 
{-@ assoc2 :: xs:[a] -> ys:[a] -> zs:[a] -> ws:[a]
          -> { xs ++ (ys ++ (zs ++ ws)) == ((xs ++ ys) ++ zs) ++ ws } @-}
assoc2 :: [a] -> [a] -> [a] -> [a] -> ()
assoc2 xs ys zs ws 
  = () {-
    assoc xs ys (zs ++ ws)
    `const` assoc (xs ++ ys) zs ws 
-}


{-@ rewrite assoc @-}
{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc [] _ _       = ()
assoc (_:xs) ys zs = assoc xs ys zs 

{-@ reflect lhs @-}
lhs xs ys zs ws = ((xs ++ ys) ++ zs) ++ ws

{-@ reflect rhs @-}
rhs xs ys zs ws = xs ++ (ys ++ (zs ++ ws))

{-@ rewriteWith assoc3 [assoc] @-} 
{-@ assoc3 :: xs:[a] -> ys:[a] -> zs:[a] -> ws:[a]
          -> { lhs xs ys zs ws = rhs xs ys zs ws } @-}
assoc3 :: [a] -> [a] -> [a] -> [a] -> ()
assoc3 xs ys zs ws = () 


{-@ reflect ++ @-}
(++)::[a] -> [a] -> [a]
[]     ++ ys = ys 
(x:xs) ++ ys = x:(xs ++ys)
