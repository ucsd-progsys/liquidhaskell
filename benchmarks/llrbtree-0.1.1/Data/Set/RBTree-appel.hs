
{-@ LIQUID "--no-termination" @-}

module Foo where

import Language.Haskell.Liquid.Prelude

data RBTree a = Leaf 
              | Node Color !(RBTree a) a !(RBTree a)
              deriving (Show)


data Color = B -- ^ Black
           | R -- ^ Red
           deriving (Eq,Show)


type RBTreeBDel a = (RBTree a, Bool)


---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

-- Definition isblack t :=
--  match t with Bk _ _ _ => True | _ => False end.
--
-- Lemma append_arb_rb n l r : rbt n l -> rbt n r ->
--  (arbt n (append l r)) /\
--  (notred l -> notred r -> rbt n (append l r)).
-- 
-- A third approach : Lemma ... with ...
-- 
-- Lemma del_arb s x n : rbt (S n) s -> isblack s -> arbt n (del x s)
-- with del_rb s x n : rbt n s -> notblack s -> rbt n (del x s).
-- Instance remove_rb s x : Rbt s -> Rbt (remove x s).

{-@ isBlack :: t:RBT a -> {v:Bool | ((Prop v) <=> (isB t))} @-} 
isBlack (Node B _ _ _) = True
isBlack _              = False

{- del :: (Ord a) => a -> t:RBT a -> {v:ARBT a | (((isB t) || (isRB v)) && ((IsB t) => (IsB v)))} @-}

{-@ invariant {v: Color | (v = R || v = B)} @-}

{-@ del              :: (Ord a) => a -> t:RBT a -> {v:ARBT a | ((isB t) || (isRB v))} @-}
del x Leaf           = Leaf
del x (Node _ a y b) = case compare x y of
   EQ -> append a b 
   LT -> case a of
           Node B _ _ _ -> lbalS (del x a) y b
           Leaf         -> Node R Leaf y b
           _            -> let zoo = Node R (del x a) y b in zoo 
   GT -> case b of
           Node B _ _ _ -> rbalS a y (del x b)
           Leaf         -> Node R a y Leaf 
           _            -> Node R a y (del x b)

{-@ append :: l:RBT a -> r:RBT a -> ARBT2 a l r @-}
append :: RBTree a -> RBTree a -> RBTree a
append = undefined

{- 
Fixpoint append (l:tree) : tree -> tree :=
 match l with
 | Leaf => fun r => r
 | Node lc ll lx lr =>
   fix append_l (r:tree) : tree :=
   match r with
   | Leaf => l
   | Node rc rl rx rr =>
     match lc, rc with
     | Red, Red =>
       let lrl := append lr rl in
       match lrl with
       | Rd lr' x rl' => Rd (Rd ll lx lr') x (Rd rl' rx rr)
       | _ => Rd ll lx (Rd lrl rx rr)
       end
     | Black, Black =>
       let lrl := append lr rl in
       match lrl with
       | Rd lr' x rl' => Rd (Bk ll lx lr') x (Bk rl' rx rr)
       | _ => lbalS ll lx (Bk lrl rx rr)
       end
     | Black, Red => Rd (append_l rl) rx rr
     | Red, Black => Rd ll lx (append lr r)
     end
   end
 end.
-}



-- Fixpoint del x t :=
--  match t with
--  | Leaf => Leaf
--  | Node _ a y b =>
--    match X.compare x y with
--    | Eq => append a b
--    | Lt =>
--      match a with
--      | Bk _ _ _ => lbalS (del x a) y b
--      | _ => Rd (del x a) y b
--      end
--    | Gt =>
--      match b with
--      | Bk _ _ _ => rbalS a y (del x b)
--      | _ => Rd a y (del x b)
--      end
--    end
--  end.



---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ deleteMin            :: RBT a -> RBT a @-}
deleteMin (Leaf)         = Leaf
deleteMin (Node _ l x r) = turnB' t
  where 
    (_, t)               = deleteMin' l x r

{-@ type ARBT2 a L R = {v:ARBT a | (((IsB L) && (IsB R)) => (isRB v))} @-}

{-@ deleteMin'                   :: l:RBT a -> a -> r:RBT a -> (a, ARBT2 a l r) @-}
deleteMin' Leaf k r              = (k, r)
deleteMin' (Node R ll lx lr) x r = (k, Node R l' x r)   where (k, l') = deleteMin' ll lx lr 
deleteMin' (Node B ll lx lr) x r = (k, lbalS l' x r )   where (k, l') = deleteMin' ll lx lr 


{-@ lbalS                             :: ARBT a -> a -> r:RBT a -> {v: ARBT a | ((IsB r) => (isRB v))} @-}
lbalS (Node R a x b) k r              = Node R (Node B a x b) k r
-- lbalS l k (Node B a y b)              = let zoo = rbal' l k (Node R a y b) in zoo 
-- lbalS l k (Node R (Node B a y b) z c) = Node R (Node B l k a) y (rbal' b z (turnR' c))
-- lbalS l k r                           = Node R l k r

{-@ rbal' :: RBT a -> a -> ARBT a -> RBT a @-}
rbal' l k (Node R b y (Node R c z d)) = Node R (Node B l k b) y (Node B c z d)
rbal' l k (Node R (Node R b y c) z d) = Node R (Node B l k b) y (Node B c z d)
rbal' l k r                           = Node B l k r

{-@ rbalS                             :: l:RBT a -> a -> ARBT a -> {v: ARBT a | ((IsB l) => (isRB v))} @-}
rbalS l k (Node R b y c)              = Node R l k (Node B b y c)
rbalS (Node B a x b) k r              = let zoo = lbal (Node R a x b) k r in zoo
rbalS (Node R a x (Node B b y c)) k r = Node R (lbal (turnR' a) x b) y (Node B c k r)
rbalS l k r                           = Node R l k r

{-@ lbal                              :: ARBT a -> a -> RBT a -> RBT a @-}
lbal (Node R (Node R a x b) y c) k r  = Node R (Node B a x b) y (Node B c k r)
lbal (Node R a x (Node R b y c)) k r  = Node R (Node B a x b) y (Node B c k r)
lbal l k r                            = Node B l k r




-- Definition rbalS l k r :=
--  match r with
--  | Rd b y c => Rd l k (Bk b y c)
--  | _ =>
--    match l with
--    | Bk a x b => lbal (Rd a x b) k r
--    | Rd a x (Bk b y c) => Rd (lbal (makeRed a) x b) y (Bk c k r)
--    | _ => Rd l k r 
--    end
--  end.



---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ turnB :: ARBT a -> RBT a @-}
turnB Leaf           = error "turnB"
turnB (Node _ l x r) = Node B l x r

{-@ turnR :: RBT a -> ARBT a @-}
turnR Leaf           = error "turnR"
turnR (Node _ l x r) = Node R l x r


{-@ turnR' :: RBT a -> ARBT a @-}
turnR' Leaf           = Leaf
turnR' (Node _ l x r) = Node R l x r


{-@ turnB' :: ARBT a -> RBT a @-}
turnB' Leaf           = Leaf
turnB' (Node _ l x r) = Node B l x r

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ type ARBTB a = (RBT a, Bool) @-}
{-@ type RBTB a = (RBT a, Bool)  @-}

{-@ type RBT a  = {v: (RBTree a) | (isRB v)} @-}
{- type ARBT a = {v: (RBTree a) | ((isARB v) && ((IsB v) => (isRB v)))} -}


{-@ type ARBT a = {v: (RBTree a) | (isARB v) } @-}

{-@ measure isRB        :: RBTree a -> Prop
    isRB (Leaf)         = true
    isRB (Node c l x r) = ((isRB l) && (isRB r) && ((Red c) => ((IsB l) && (IsB r))))
  @-}

{-@ measure isARB        :: (RBTree a) -> Prop
    isARB (Leaf)         = true 
    isARB (Node c l x r) = ((isRB l) && (isRB r))
  @-}

{-@ measure col         :: RBTree a -> Color
    col (Node c l x r)  = c
    col (Leaf)          = B
  @-}

{-@ measure isB        :: RBTree a -> Prop
    isB (Leaf)         = false
    isB (Node c l x r) = c == B 
  @-}

{-@ predicate IsB T = not (Red (col T)) @-}
{-@ predicate Red C = C == R            @-}

-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ predicate Invs V = ((Inv1 V) && (Inv2 V))               @-}
{-@ predicate Inv1 V = (((isARB V) && (IsB V)) => (isRB V)) @-}
{-@ predicate Inv2 V = ((isRB v) => (isARB v))              @-}

{-@ invariant {v: RBTree a | (Invs v)} @-}

{-@ inv            :: RBTree a -> {v:RBTree a | (Invs v)} @-}
inv Leaf           = Leaf
inv (Node c l x r) = Node c (inv l) x (inv r)
