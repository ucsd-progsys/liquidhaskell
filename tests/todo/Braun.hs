{-@ LIQUID "--reflection" @-}
module Braun where 

import qualified Data.Set as S 

{-@ data Tree [size] a = 
      Empty 
    | Node { root  :: a 
           , left  :: Tree {v:a | root <= v } 
           , right :: {r : Tree {v:a | root <= v} | okSize left r }
           }
  @-}

{-@ inline okSize @-}
okSize :: Tree a -> Tree a -> Bool
okSize l r = size l == size r || size l == size r + 1 

data Tree a 
  = Empty 
  | Node { val   :: a 
         , left  :: Tree a 
         , right :: Tree a 
         }
        
{-@ measure size @-}
{-@ size :: Tree a -> Nat @-}

size :: Tree a -> Int 
size Empty        = 0
size (Node _ l r) = 1 + size l + size r

{-@ measure tElems @-}
tElems :: (Ord a) => Tree a -> S.Set a
tElems Empty        = S.empty
tElems (Node x l r) = sAdd1 x (tElems l `S.union` tElems r)

{-@ inline sAdd1 @-}
sAdd1 :: (Ord a) => a -> S.Set a -> S.Set a
sAdd1 x s = S.singleton x `S.union` s

{-@ empty :: {v:_ | tElems v = S.empty} @-}
empty :: Tree a 
empty = Empty

--------------------------------------------------------------------------------------------
{-@ add :: x:_ -> t:_ -> {tx:_ | size tx = 1 + size t && tElems tx = sAdd1 x (tElems t)} @-}
--------------------------------------------------------------------------------------------
add :: (Ord a) => a -> Tree a -> Tree a
add x Empty        = Node x Empty Empty
add x (Node y l r) 
  | x <= y         = Node x (add y r) l
  | otherwise      = Node y (add x r) l


--------------------------------------------------------------------------------------------
{-@ reflect get_min @-}
{-@ get_min :: {t:_ | 0 < size t} -> a @-}
get_min :: Tree a -> a 
get_min (Node x _ _) = x  

{-@ lem_min :: {t:_ | 0 < size t} -> TT @-}
lem_min :: (Ord a) => Tree a -> Bool
lem_min (Node x l r) = all_vals l (x <=) && all_vals r (x <=)

{-@ all_vals :: forall <p :: a -> Bool>. Tree (a<p>) -> (a<p> -> TT) -> TT @-}
all_vals :: Tree a -> (a -> Bool) -> Bool
all_vals Empty _        = True
all_vals (Node x l r) p = p x && all_vals l p && all_vals r p

--------------------------------------------------------------------------------------------
remove_min :: (Ord a) => Tree a -> Tree a
remove_min (Node _ l r) = merge l r


merge l Empty = l
merge Empty r = r  
merge (Node lx ll lr) (Node rx rl rr) 
  | lx <= rx  = Node lx (Node rx rl rr) (merge ll lr) 
  | otherwise = Node rx (             ) (Node lx ll lr)


{-@ extract     :: tx:Tree a -> (x :: a, {t:Tree a | size t = size tx - 1 && tElts tx = sAdd1 x (tElts t)}) @-}
{-@ replaceRoot :: x:a -> t:{_ | 0 < size t} -> {v:_ | size v == size t && tElts v = sAdd1 x (tElts' t)} @-}

rr x (Node _ (Node (lx ll lr)) (Node (rx rl rr))) 
  | x <= lx && x <= lr = undefined
  | x <= lx && x >  lr = undefined

{-@ measure tElts' @-}
tElts' :: (Ord a) => Tree a -> S.Set a
tElts' Empty        = S.empty
tElts' (Node _ l r) = (tElts l) `S.union` (tElts r)



{- 

module BraunHeaps

  use int.Int
  use bintree.Tree
  use export bintree.Size
  use export bintree.Occ

  type elt

  val predicate le elt elt

  clone relations.TotalPreOrder with type t = elt, predicate rel = le, axiom .

  (* [e] is no greater than the root of [t], if any *)
  let predicate le_root (e: elt) (t: tree elt) = match t with
    | Empty -> true
    | Node _ x _ -> le e x
  end

  predicate heap (t: tree elt) = match t with
    | Empty      -> true
    | Node l x r -> le_root x l && heap l && le_root x r && heap r
  end

  function minimum (tree elt) : elt
  axiom minimum_def: forall l x r. minimum (Node l x r) = x

  predicate is_minimum (x: elt) (t: tree elt) =
    mem x t && forall e. mem e t -> le x e

  (* the root is the smallest element *)
  let rec lemma root_is_min (t: tree elt) : unit
     requires { heap t && 0 < size t }
     ensures  { is_minimum (minimum t) t }
     variant  { t }
  = let Node l _ r = t in
    if not is_empty l then root_is_min l;
    if not is_empty r then root_is_min r

  predicate inv (t: tree elt) = match t with
  | Empty      -> true
  | Node l _ r -> (size l = size r || size l = size r + 1) && inv l && inv r
  end

  let empty () : tree elt
    ensures { heap result }
    ensures { inv result }
    ensures { size result = 0 }
    ensures { forall e. not (mem e result) }
    = Empty

  let get_min (t: tree elt) : elt
    requires { heap t && 0 < size t }
    ensures  { result = minimum t }
  =
    match t with
      | Empty      -> absurd
      | Node _ x _ -> x
    end

  let rec add (x: elt) (t: tree elt) : tree elt
    requires { heap t }
    requires { inv t }
    variant  { t }
    ensures  { heap result }
    ensures  { inv result }
    ensures  { occ x result = occ x t + 1 }
    ensures  { forall e. e <> x -> occ e result = occ e t }
    ensures  { size result = size t + 1 }
  =
    match t with
    | Empty ->
        Node Empty x Empty
    | Node l y r ->
        if le x y then
          Node (add y r) x l
        else
          Node (add x r) y l
    end

  let rec extract (t: tree elt) : (elt, tree elt)
     requires { heap t }
     requires { inv t }
     requires { 0 < size t }
     variant  { t }
     ensures  { let e, t' = result in
                heap t' && inv t' && size t' = size t - 1 &&
                occ e t' = occ e t - 1 &&
                forall x. x <> e -> occ x t' = occ x t }
  =
    match t with
    | Empty ->
        absurd
    | Node Empty y r ->
        assert { r = Empty };
        y, Empty
    | Node l y r ->
        let x, l = extract l in
        x, Node r y l
    end

  let rec replace_min (x: elt) (t: tree elt)
    requires { heap t }
    requires { inv t }
    requires { 0 < size t }
    variant  { t }
    ensures  { heap result }
    ensures  { inv result }
    ensures  { if x = minimum t then occ x result = occ x t
               else occ x result = occ x t + 1 &&
                    occ (minimum t) result = occ (minimum t) t - 1 }
    ensures  { forall e. e <> x -> e <> minimum t -> occ e result = occ e t }
    ensures  { size result = size t }
  =
    match t with
    | Node l _ r ->
        if le_root x l && le_root x r then
          Node l x r
        else
          let lx = get_min l in
          if le_root lx r then
            (* lx <= x, rx necessarily *)
            Node (replace_min x l) lx r
          else
            (* rx <= x, lx necessarily *)
            Node l (get_min r) (replace_min x r)
    | Empty ->
        absurd
    end

  let rec merge (l r: tree elt) : tree elt
    requires { heap l && heap r }
    requires { inv l && inv r }
    requires { size r <= size l <= size r + 1 }
    ensures  { heap result }
    ensures  { inv result }
    ensures  { forall e. occ e result = occ e l + occ e r }
    ensures  { size result = size l + size r }
    variant  { size l + size r }
  =
    match l, r with
    | _, Empty ->
        l
    | Node ll lx lr, Node _ ly _ ->
        if le lx ly then
          Node r lx (merge ll lr)
        else
          let x, l = extract l in
          Node (replace_min x r) ly l
    | Empty, _ ->
        absurd
    end

  let remove_min (t: tree elt) : tree elt
    requires { heap t }
    requires { inv t }
    requires { 0 < size t }
    ensures  { heap result }
    ensures  { inv result }
    ensures  { occ (minimum t) result = occ (minimum t) t - 1 }
    ensures  { forall e. e <> minimum t -> occ e result = occ e t }
    ensures  { size result = size t - 1 }
  =
    match t with
      | Empty      -> absurd
      | Node l _ r -> merge l r
    end

The size of a Braun tree can be computed in time O(log^2(n))

from Three Algorithms on Braun Trees (Functional Pearl) Chris Okasaki J. Functional Programming 7 (6) 661–666, November 1997

  use int.ComputerDivision

  let rec diff (m: int) (t: tree elt)
    requires { inv t }
    requires { 0 <= m <= size t <= m + 1 }
    variant  { t }
    ensures  { size t = m + result }
  = match t with
    | Empty ->
        0
    | Node l _ r ->
        if m = 0 then
          1
        else if mod m 2 = 1 then
          (* m = 2k + 1  *)
          diff (div m 2) l
        else
          (* m = 2k + 2 *)
          diff (div (m - 1) 2) r
    end

  let rec fast_size (t: tree elt) : int
    requires { inv t}
    variant  { t }
    ensures  { result = size t }
  =
    match t with
    | Empty -> 0
    | Node l _ r -> let m = fast_size r in 1 + 2 * m + diff m l
    end

A Braun tree has a logarithmic height

  use bintree.Height
  use int.Power

  let rec lemma size_height (t1 t2: tree elt)
    requires { inv t1 && inv t2 }
    variant  { size t1 + size t2 }
    ensures  { size t1 >= size t2 -> height t1 >= height t2 }
  = match t1, t2 with
    | Node l1 _ r1, Node l2 _ r2 ->
        size_height l1 l2;
        size_height r1 r2
    | _ ->
        ()
    end

  let rec lemma inv_height (t: tree elt)
    requires { inv t }
    variant  { t }
    ensures  { size t > 0 ->
               let h = height t in power 2 (h-1) <= size t < power 2 h }
  = match t with
    | Empty | Node Empty _ _ ->
        ()
    | Node l _ r ->
        let h = height t in
        assert { height l = h-1 };
        inv_height l;
        inv_height r
    end

end


-}
