{- Example of AVL trees by michaelbeaumont -}

{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--totality"       @-}

module AVL (AVL, empty, singleton, insert, insert', delete) where

-- import Language.Haskell.Liquid.Prelude (liquidAssume)

-- Test
main = do
    mapM_ print [a, b, c, d]
  where
    a = singleton 5 
    b = insert 2 a
    c = insert 3 b
    d = insert 7 c

--------------------------------------------------------------------------------------------
-- | Datatype Definition ------------------------------------------------------------------- 
--------------------------------------------------------------------------------------------

data AVL a = Leaf | Node { key :: a, l::AVL a, r:: AVL a, ah :: Int } deriving Show

{-@ data AVL [ht] a = Leaf | Node { key :: a
                                  , l   :: AVLL a key
                                  , r   :: {v: AVLR a key | HtBal l v 1}
                                  , ah  :: {v:Nat | HtBal l r 1 && Ht v l r}
                                  }                                          @-}

-- | Left and Right Tree Ordering --------------------------------------------------------- 

{-@ type AVLL a X = AVL {v:a | v < X}                                        @-}
{-@ type AVLR a X = AVL {v:a | X < v}                                        @-}

-- | Height is actual height --------------------------------------------------------------

{-@ invariant {v:AVL a | 0 <= ht v && ht v = getHeight v} @-}

{-@ inv_proof  :: t:AVL a -> {v:_ | 0 <= ht t && ht t = getHeight t } @-}
inv_proof Leaf           = True 
inv_proof (Node k l r n) = inv_proof l && inv_proof r

-- | Logical Height Definition ------------------------------------------------------------ 

{-@ measure ht @-}
ht                :: AVL a -> Int
ht Leaf            = 0
ht (Node _ l r _) = if ht l > ht r then 1 + ht l else 1 + ht r


-- | Predicate Aliases -------------------------------------------------------------------- 

{-@ predicate HtBal L R N  = 0 <= ht L - ht R + N && ht L - ht R <= N               @-}
{-@ predicate Ht N L R     = N = if (ht L) > (ht R) then (1 + ht L) else (1 + ht R) @-}
{-@ predicate HtDiff S T D = ht S - ht T == D                                       @-}
{-@ predicate EqHt S T     = HtDiff S T 0                                           @-}
{-@ predicate NoHeavy    T = bFac T == 0                                            @-}
{-@ predicate LeftHeavy  T = bFac T == 1                                            @-}
{-@ predicate RightHeavy T = bFac T == -1                                           @-}
{-@ predicate Eq1 S T      = EqHt T S || HtDiff T S 1                               @-}
{-@ predicate RBal L R T   = if (ht L >= ht R) then (Eq1 L T) else Eq1 R T          @-}

--------------------------------------------------------------------------------------------
-- | Constructor & Destructor  -------------------------------------------------------------
--------------------------------------------------------------------------------------------

-- | Smart Constructor (fills in height field) ---------------------------------------------

{-@ tree   :: x:a -> l:AVLL a x -> r:{AVLR a x | HtBal l r 1} -> {v:AVL a | Ht (ht v) l r} @-}
tree v l r = Node v l r (mkHt l r)

{-@ mkHt   :: l:_ -> r:_ -> {v:Nat | Ht v l r} @-}
mkHt       :: AVL a -> AVL a -> Int
mkHt l r   = if hl > hr then 1 + hl else 1 + hr
  where
    hl     = getHeight l
    hr     = getHeight r


-- | Compute Tree Height -------------------------------------------------------------------
    
{-@ measure getHeight @-}
{-@ getHeight            :: t:_ -> {v:Nat | v = ht t} @-}
getHeight Leaf           = 0
getHeight (Node _ _ _ n) = n


-- | Compute Balance Factor ----------------------------------------------------------------

{-@ measure bFac @-}
{-@ bFac :: t:AVL a -> {v:Int | v = bFac t && 0 <= v + 1 && v <= 1} @-}
bFac Leaf           = 0
bFac (Node _ l r _) = getHeight l - getHeight r 

{-@ htDiff :: s:AVL a -> t: AVL a -> {v: Int | HtDiff s t v} @-}
htDiff     :: AVL a -> AVL a -> Int
htDiff l r = getHeight l - getHeight r


--------------------------------------------------------------------------------------------
-- | API: Empty ---------------------------------------------------------------------------- 
--------------------------------------------------------------------------------------------
             
{-@ empty :: {v: AVL a | ht v == 0} @-}
empty = Leaf

--------------------------------------------------------------------------------------------
-- | API: Singleton ------------------------------------------------------------------------ 
--------------------------------------------------------------------------------------------

{-@ singleton :: a -> {v: AVL a | ht v == 1 } @-}
singleton a = tree a empty empty 

--------------------------------------------------------------------------------------------
-- | API: Insert 1 (Leroy) ----------------------------------------------------------------- 
--------------------------------------------------------------------------------------------

{-@ insert' :: a -> s:AVL a -> {t: AVL a | Eq1 s t} @-}
insert' a Leaf             = singleton a
insert' a t@(Node v l r n) = case compare a v of
    LT -> bal v (insert' a l) r 
    GT -> bal v l (insert' a r) 
    EQ -> t

--------------------------------------------------------------------------------------------
-- | API: Insert 2 (Beaumont) -------------------------------------------------------------- 
--------------------------------------------------------------------------------------------

{-@ insert :: a -> s:AVL a -> {t: AVL a | Eq1 s t} @-}
insert a Leaf             = singleton a
insert a t@(Node v _ _ _) = case compare a v of
    LT -> insL a t 
    GT -> insR a t
    EQ -> t

{-@ insL :: x:a -> s:{AVL a | x < key s && ht s > 0} -> {t: AVL a | Eq1 s t} @-}
insL a (Node v l r _)
  | leftBig && bl' > 0 = balLL v l' r
  | leftBig && bl' < 0 = balLR v l' r
  | leftBig            = balL0 v l' r
  | otherwise          = tree v l' r
  where
    leftBig            = siblDiff > 1
    siblDiff           = htDiff l' r
    l'                 = insert a l
    bl'                = bFac l'
   
{-@ insR :: x:a -> s:{AVL a | key s < x && ht s > 0} -> {t: AVL a | Eq1 s t} @-}
insR a (Node v l r _)
  | rightBig && br' > 0  = balRL v l r'
  | rightBig && br' < 0  = balRR v l r'
  | rightBig             = balR0 v l r'
  | otherwise            = tree v l r'
  where
    rightBig             = siblDiff > 1
    siblDiff             = htDiff r' l
    r'                   = insert a r
    br'                  = bFac r'

--------------------------------------------------------------------------------------------
-- | API: Delete --------------------------------------------------------------------------- 
--------------------------------------------------------------------------------------------

{-@ delete               :: a -> s:AVL a -> {t: AVL a | Eq1 t s} @-}
delete _ Leaf            = Leaf
delete a (Node v l r _)  = case compare a v of
                            LT -> bal v (delete a l) r 
                            GT -> bal v l (delete a r) 
                            EQ -> merge v l r

merge                    :: a -> AVL a -> AVL a -> AVL a 
merge _ Leaf t           = t
merge _ t Leaf           = t
merge v t1 t2            = bal a t1 t2'
  where
    (a, t2')             = getMin t2
                        
getMin (Node x Leaf r _) = (x, r)
getMin (Node x l r _)    = (x', bal x l' r)
  where
    (x', l')             = getMin l

--------------------------------------------------------------------------------------------
-- | Bal ----------------------------------------------------------------------------- 
--------------------------------------------------------------------------------------------

{-@ bal :: x:a -> l:AVLL a x -> r:{AVLR a x | HtBal l r 2} -> {t: AVL a | (HtBal l r 1 => Ht (ht t) l r) && RBal l r t} @-}
bal v l r
  | leftBig  && bl > 0 = balLL v l r -- l
  | leftBig  && bl < 0 = balLR v l r -- l 
  | leftBig            = balL0 v l r -- l + 1
  | rightBig && br > 0 = balRL v l r -- r
  | rightBig && br < 0 = balRR v l r -- r
  | rightBig           = balR0 v l r -- r + 1
  | otherwise          = tree v l r
  where
    leftBig            = siblDiff     > 1
    rightBig           = siblDiff + 1 < 0
    siblDiff           = htDiff l r
    bl                 = bFac l
    br                 = bFac r

{-@ balL0 :: x:a -> l:{AVLL a x | NoHeavy l} -> r:{AVLR a x | HtDiff l r 2} -> {t:AVL a | ht t = ht l + 1 } @-}
balL0 v (Node lv ll lr _) r
  = tree lv ll (tree v lr r)

{-@ balLL :: x:a -> l:{AVLL a x | LeftHeavy l } -> r:{AVLR a x | HtDiff l r 2} -> {t:AVL a | EqHt t l} @-}
balLL v (Node lv ll lr _) r
  = tree lv ll (tree v lr r)

{-@ balLR :: x:a -> l:{AVLL a x | RightHeavy l } -> r:{AVLR a x | HtDiff l r 2} -> {t: AVL a | EqHt t l } @-}
balLR v (Node lv ll (Node lrv lrl lrr _) _) r
  = tree lrv (tree lv ll lrl) (tree v lrr r)

{-@ balR0 :: x:a -> l: AVLL a x -> r: {AVLR a x | NoHeavy r && HtDiff r l 2 } -> {t: AVL a | ht t = ht r + 1} @-}
balR0 v l (Node rv rl rr _)
  = tree rv (tree v l rl) rr

{-@ balRR :: x:a -> l: AVLL a x -> r:{AVLR a x | RightHeavy r && HtDiff r l 2 } -> {t: AVL a | EqHt t r } @-}
balRR v l (Node rv rl rr _)
  = tree rv (tree v l rl) rr

{-@ balRL :: x:a -> l: AVLL a x -> r:{AVLR a x | LeftHeavy r && HtDiff r l 2} -> {t: AVL a | EqHt t r } @-}
balRL v l (Node rv (Node rlv rll rlr _) rr _)
  = tree rlv (tree v l rll) (tree rv rlr rr) 
                                                      
