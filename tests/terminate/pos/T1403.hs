{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module T1403 where

data List a = Nil | Cons a (List a)

{-@ reflect rev @-}
rev :: List a -> List a
rev Nil         = Nil
rev (Cons x xs) = app (rev xs) (Cons x Nil)

{-@ reflect app @-}
app :: List a -> List a -> List a
app Nil ys         = ys
app (Cons x xs) ys = Cons x (app xs ys)


{-@ reflect mirror @-}
mirror :: Tree a -> Tree a
mirror Tip          = Tip
mirror (Node l a r) = Node (mirror r) a (mirror l)

data Tree a = Tip | Node (Tree a) a (Tree a)

{-@ reflect contents @-}
contents :: Tree a -> List a
contents Tip          = Nil
contents (Node l a r) = app (app (contents l) (Cons a Nil)) (contents r)

{-@ thm_mirror_contents :: t:_ -> { contents (mirror t) = rev (contents t) } @-}
thm_mirror_contents :: Tree a -> Proof
thm_mirror_contents Tip
   = ()
thm_mirror_contents (Node l a r)
   = contents (mirror (Node l a r))
      ? thm_mirror_contents r
      ? thm_mirror_contents l
--    === undefined                   -- <<<<< Adding this line yields "Termination Error?"
   ==! rev (contents (Node l a r))
   *** ()


infixl 3 ===
{-@ (===) :: x:a -> y:{a | y == x} -> {v:a | v == x && v == y} @-}
(===) :: a -> a -> a
_ === y  = y

infixl 3 ==!
{-@ assume (==!) :: x:a -> y:a -> {v:a | v == x && v == y} @-}
(==!) :: a -> a -> a
(==!) _ y = y

infixl 3 ?

{-@ (?) :: forall a b <pa :: a -> Bool, pb :: b -> Bool>. a<pa> -> b<pb> -> a<pa> @-}
(?) :: a -> b -> a
x ? _ = x
{-# INLINE (?)   #-}

infixl 3 ***
{- assume (***) :: a -> p:_ -> { if (isAdmit p) then false else true } @-}
(***) :: a -> b -> Proof
_ *** _ = ()

type Proof = ()
