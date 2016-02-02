module List where


--------------------------------------------------------------------------------
--- Code
--------------------------------------------------------------------------------
data List a = Nil | Cons a (List a)
infixr `Cons`

insert :: Int -> List Int -> List Int
insert x ys = insert' x ys

insert' x Nil
  = Cons x Nil
insert' x (y `Cons` ys)
  | x < y
  = x `Cons` y `Cons` ys
  | x == y
  = y `Cons` ys
  | otherwise
  = y `Cons` insert' x ys

{-@ data List a <p:: a -> a -> Prop> =
      Nil | Cons (zoo::a) (zoog::List <p> (a<p zoo>))
  @-}

{-@ measure llen :: List a -> Int
    llen(Nil) = 0
    llen(Cons x xs) = 1 + llen(xs)
  @-}

{-@ type SortedList a = List <{\x y -> x < y}> a @-}

{-@ insert :: n:Int -> xs:SortedList Int -> SortedList Int @-}

