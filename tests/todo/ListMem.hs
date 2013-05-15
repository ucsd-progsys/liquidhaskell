module ListMem where


import Data.Set hiding (partition)


{-@ member' :: Eq a 
           => x:a 
           -> xs:[a] 
           -> {v:([{vv:a|vv=x}], [{vv:a|vv!=x}]) | (PairEqElts xs v)}
  @-}
member' :: Eq a => a -> [a] -> ([a], [a])
member' x ls = partition (cmp x) ls 

{-@ member :: Eq a 
           => x:a 
           -> xs:[a] 
           -> {v:Bool|((Prop v) <=> (ListElt x xs))}
  @-}
member :: Eq a => a -> [a] -> Bool
member x ls 
  = case partition (cmp x) ls of
     ([], _) -> False -- can not prove this!
     (_, _)  -> True

{-@ predicate ListElt N LS =
       (Set_mem N (listElts LS)) 
  @-}

{-@ predicate PairEqElts X P =
 ((listElts X) = (Set_cup (listElts (getFst P)) (listElts (getSnd P))))
  @-}

{-@ predicate UnionElts X Y Z W =
       ((listElts X) = (Set_cup (listElts Y) (Set_cup (listElts Z) (listElts W)))) 
  @-}

{-@ measure getFst :: (a, b) -> a
    getFst(a, b) = a 
  @-}

{-@ measure getSnd :: (a, b) -> b
    getSnd(a, b) = b
  @-}


{-@ cmp :: Eq a 
        => x:a 
        -> y:a 
        -> Either {v:a| ((v = y) && (v = x))} 
                  {v:a| ((v != x) && (v = y))} 
  @-}
cmp :: Eq a => a -> a ->  Either a a
cmp x y | x == y    = Left  y
        | otherwise = Right y


{-@ partition :: forall <p :: a -> Prop, q :: a -> Prop>.
                 (x:a -> Either {v:a<p>|v = x} {v:a<q>|v=x})
              -> xs:[a] 
              -> {v:([a<p>], [a<q>]) | (PairEqElts xs v) }
  @-}
partition :: (a -> Either a a) -> [a] -> ([a], [a])
partition f xs = partition' f xs xs ([], [])

{-@ partition' :: forall <p :: a -> Prop, q :: a -> Prop>.
                 (x:a -> Either {v:a<p>|v = x} {v:a<q>|v=x})
              -> init:[a] 
              -> xs:[a] 
              -> ack:{v:([a<p>], [a<q>]) | ((listElts init) = (Set_cup (listElts xs) (Set_cup (listElts (getFst v)) (listElts (getSnd v))))) }
              -> {v:([a<p>], [a<q>]) | (listElts init) = (Set_cup (listElts (getFst v)) (listElts (getSnd v)))}
  @-}
partition' :: (a -> Either a a) -> [a] -> [a] -> ([a], [a]) -> ([a], [a])
partition' _ a [] (x, y) = (x, y)
partition' f a (x:xs) (pos, neg) 
  = case f x of
    Left _  -> partition' f a xs (x:pos, neg) 
    Right _ -> partition' f a xs (pos, x:neg) 

