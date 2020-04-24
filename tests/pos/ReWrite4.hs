module ReWrite8 where

{-@ LIQUID "--savequery" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix ++ @-}

import Prelude hiding ((++))

data MyList a = MyNil | Cons a (MyList a)

{-@ reflect ++ @-}
(++)::MyList a -> MyList a -> MyList a
MyNil       ++ ys = ys
(Cons x xs) ++ ys = Cons x (xs ++ ys)


{-@ concatIdent :: xs : MyList a -> { xs = xs ++ MyNil } @-}
concatIdent :: MyList a -> ()
concatIdent MyNil       = ()
concatIdent (Cons _ xs) = concatIdent xs

{-@ rewriteWith concatIdent' [concatIdent] @-}
{-@ concatIdent' :: xs : MyList a -> { xs = xs ++ MyNil } @-}
concatIdent' :: MyList a -> ()
concatIdent' _ = ()


