Case Study: AVL Trees
=====================

\begin{comment}
\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--diffcheck"     @-}

module AVL where

main :: IO ()
main = return ()

\end{code}
\end{comment}

\begin{code}
-- Source: https://gist.github.com/gerard/109729

-- | PORTED from: http://docs.camlcity.org/docs/godipkg/4.00/godi-ocaml/lib/ocaml/std-lib/map.ml


data AVL k v = Leaf
             | Node { key :: k
                    , val :: v
                    , lt  :: AVL k v
                    , rt  :: AVL k v
                    , ht  :: Int }
               deriving (Show, Eq)

{-@ data AVL k v = Leaf
                 | Node { key :: k
                        , val :: v
                        , lt  :: AVLL k v key
                        , rt  :: AVLR k v key
                        , ht  :: AVLH lt rt 
                        }
  @-}

{-@ type AVLL k v Key    = AVL {k:k | k < Key} v             @-}
{-@ type AVLR k v Key    = AVL {k:k | Key < k} v             @-}
{-@ type AVLH L R        = {v:Nat   | Ht v L R && Bal L R 2} @-}
{-@ type AVLN k v N      = {v:AVL k v | tht v = N}           @-}

{-@ predicate LeMax1 V X Y = V <= if X >= Y then 1+X else 1+Y   @-}
{-@ predicate EqMax1 V X Y = V = if X >= Y then 1+X else 1+Y   @-}
{-@ predicate Diff X Y N = 0 <= X - Y + N && X - Y <= N      @-}
{-@ predicate Bal L R N  = Diff (tht L) (tht R) N      @-}
{-@ predicate Ht V L R   = EqMax1 V (tht L) (tht R)      @-}

{-@ measure tht          :: AVL k v -> Int
    tht (Leaf)           = 0
    tht (Node k v l r z) = if (tht l >= tht r) then (1 + tht l) else (1 + tht r)
  @-}

{-@ height              :: t:_ -> {v:Nat | v = tht t} @-}
height (Leaf)           = 0 :: Int
height (Node k v l r z) = if (height l >= height r) then (1 + height l) else (1 + height r)
 
                        
empty = Leaf

{-@ ht :: t:AVL k v -> {v:Nat | v = tht t}  @-}

{-@ create     :: key:k -> v -> l:AVLL k v key -> r:{AVLR k v key | Bal l r 2} -> {v:AVL k v | Ht (tht v) l r} @-}
create k v l r = Node k v l r (nodeHeight l r) 

{-@ nodeHeight :: l:_ -> r:_ -> {v:Nat | Ht v l r} @-}
nodeHeight l r = h
  where
   h           = if hl >= hr then hl + 1 else hr + 1
   hl          = height l
   hr          = height r 

{-@ singleton  :: k -> v -> AVLN k v 1 @-}
singleton k v  = Node k v Leaf Leaf 1 

{-@ fox :: k -> v -> thing:AVL k v -> {v: AVL k v | tht thing - 1 <= tht v && tht v <= tht thing + 1} @-}
fox :: k -> v -> AVL k v -> AVL k v
fox key val tree = error "z"



{-@ add :: k -> v -> t:AVL k v -> {v: AVL k v | tht t - 1 <= tht v && tht v <= tht t + 1} @-}
add k' v' t@(Node k v l r h)
  -- RJ: This case is obviously fine
  
  | k' == k     = Node k' v' l r h  

  -- RJ: Maddeningly, this case is fine too
                  
--   | k' <  k     = let mickey = fox k' v' l
--                   in
--                      bal k v mickey r   

  -- RJ: HEREHEREHERE this is the problem (I GIVE UP)
  | k < k'      = let mouse = fox k' v' r  in
                      bal k v l mouse 

add k' v' Leaf  = singleton k' v'

{-@ bal         :: key:k -> v -> l:AVLL k v key -> r:{AVLR k v key | Bal l r 3} -> {v:AVL k v  | tht l <= tht v && tht r <= tht v && (tht l >= tht r => tht v <= 1 + tht l) && (tht r >= tht l => tht v <= 1 + tht r) } @-}
bal :: k -> v -> AVL k v -> AVL k v -> AVL k v
bal k v l r 
  | hl > hr + 2 = balL   k v l r
  | hr > hl + 2 = balR   k v l r 
  | otherwise   = create k v l r 
  where
    hl          = height l
    hr          = height r

{-@ balL :: k:_ -> v:_ -> l:AVLL k v k -> r:AVLN {v:_ | k < v} v {(tht l) - 3} -> {v:AVL k v | tht l <= tht v && tht v <= 1 + tht l} @-}    
balL k v l@(Node lk lv ll lr _) r
  | height ll >= height lr = let tmp = create k v lr r in lAssert (height tmp <= height l) $ create lk lv ll tmp
  | otherwise              = case lr of
                               Node lrk lrv lrl lrr _ -> create lrk lrv (create lk lv ll lrl) (create k v lrr r)
                               Leaf                   -> die  "all done" 

-- balL k v (Node lk lv ll lr@(Node lrk lrv lrl lrr _) _) r
--   | height ll < height lr  = create lrk lrv (create lk lv ll lrl) (create k v lrr r)

{-@ balR :: k:_ -> v:_ -> l:AVLL k v k -> r:AVLN {v:_ | k < v} v {(tht l) + 3} -> {v: AVL k v | tht r <= tht v && tht v <= 1 + tht r} @-}    
balR k v l r@(Node rk rv rl rr _) 
  | height rr >= height rl = create rk rv (create k v l rl) rr
  | otherwise              = case rl of 
                              Node rlk rlv rll rlr _ -> create rlk rlv (create k v l rll) (create rk rv rlr rr)
                              Leaf                   -> die "all done"
                              
-- balR k v l r@(Node rk rv rl@(Node rlk rlv rll rlr _) rr _)
--   | height rr < height rl  = create rlk rlv (create k v l rll) (create rk rv rlr rr) 

{-@ die :: {v:String | false } -> a @-}
die x = error x

{-@ lAssert    :: {v:Bool | Prop v} -> a -> a @-}
lAssert True x = x
lAssert _    z = z
    
--      let hl = match l with Empty -> 0 | Node(_,_,_,_,h) -> h in
--      let hr = match r with Empty -> 0 | Node(_,_,_,_,h) -> h in
--      if hl > hr + 2 then begin
--        match l with
--          Empty -> invalid_arg "Map.bal"
--        | Node(ll, lv, ld, lr, _) ->
--            if height ll >= height lr then
--              create ll lv ld (create lr x d r)
--            else begin
--              match lr with
--                Empty -> invalid_arg "Map.bal"
--              | Node(lrl, lrv, lrd, lrr, _)->
--                  create (create ll lv ld lrl) lrv lrd (create lrr x d r)
--            end
--      end else if hr > hl + 2 then begin
--        match r with
--          Empty -> invalid_arg "Map.bal"
--        | Node(rl, rv, rd, rr, _) ->
--            if height rr >= height rl then
--              create (create l x d rl) rv rd rr
--            else begin
--              match rl with
--                Empty -> invalid_arg "Map.bal"
--              | Node(rll, rlv, rld, rlr, _) ->
--                  create (create l x d rll) rlv rld (create rlr rv rd rr)
--            end
--      end else
--        Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))


\end{code}

Ideal

data AVK k v = Leaf | Node { key :: _
                           , val :: _
                           , lt  :: _
                           , rt  :: _
                           , ht :: {v:Int | v = max1 (height lt) (height rt)}
                           }

@ measure max1 
max1 x y = 1 + if (x > y) then x else y

@ measure height
height                  :: AVL k v -> Int
height (Node _ _ l r _) = max1 (height l) (height r)
height _                = 0



inorder :: BT -> [Int]
inorder L = []
inorder (N v t u) = inorder t ++ [v] ++ inorder u

left (N _ t _) = t
right (N _ _ u) = u
value (N v _ _) = v



-- FIXME: Could be cleaner BT -> Int using left and right of BT
balFactor :: BT -> BT -> Int
balFactor t u = (depth t) - (depth u)

-- Tricky but easy: we return a binary list with the route to the node
search :: BT -> Int -> Maybe [Int]
search L s = Nothing
search (N v t u) s 
    | v == s                  = Just []
    | (search t s) /= Nothing = fmap ((:) 0) (search t s)
    | (search u s) /= Nothing = fmap ((:) 1) (search u s)
    | otherwise               = Nothing

-- Complementary to search: get the node with the path
getelem :: BT -> [Int] -> Maybe Int
getelem L _ = Nothing
getelem (N v _ _) [] = Just v
getelem (N v t u) (x:xs)
    | x == 0    = getelem t xs
    | otherwise = getelem u xs

-- If you get confused (I do), check this nice picture:
-- http://en.wikipedia.org/wiki/Image:Tree_Rebalancing.gif
balanceLL (N v (N vl tl ul) u)              = (N vl tl (N v ul u))
balanceLR (N v (N vl tl (N vlr tlr ulr)) u) = (N vlr (N vl tl tlr) (N v ulr u))
balanceRL (N v t (N vr (N vrl trl url) ur)) = (N vrl (N v t trl) (N vr url ur)) 
balanceRR (N v t (N vr tr ur))              = (N vr (N v t tr) ur)

-- Balanced insert
insert :: BT -> Int -> BT
insert L i = (N i L L)
insert (N v t u) i
    | i == v = (N v t u)
    | i < v && (balFactor ti u) ==  2 && i < value t = balanceLL (N v ti u)
    | i < v && (balFactor ti u) ==  2 && i > value t = balanceLR (N v ti u)
    | i > v && (balFactor t ui) == -2 && i < value u = balanceRL (N v t ui)
    | i > v && (balFactor t ui) == -2 && i > value u = balanceRR (N v t ui)
    | i < v  = (N v ti u)
    | i > v  = (N v t ui)
        where ti = insert t i
              ui = insert u i

-- Balanced delete
delete :: BT -> Int -> BT
delete L d = L
delete (N v L L) d = if v == d then L else (N v L L)
delete (N v t L) d = if v == d then t else (N v t L)
delete (N v L u) d = if v == d then u else (N v L u)
delete (N v t u) d
    | v == d                            = (N mu t dmin)
    | v > d && abs (balFactor dt u) < 2 = (N v dt u)
    | v < d && abs (balFactor t du) < 2 = (N v t du)
    | v > d && (balFactor (left u) (right u)) < 0 = balanceRR (N v dt u) 
    | v < d && (balFactor (left t) (right t)) > 0 = balanceLL (N v t du)
    | v > d                                       = balanceRL (N v dt u)
    | v < d                                       = balanceLR (N v t du)
        where dmin = delete u mu
              dt   = delete t d
              du   = delete u d
              mu   = btmin u

btmin = head . inorder

-- Test Functions
load :: BT -> [Int] -> BT
load t []     = t
load t (x:xs) = insert (load t xs) x

unload :: BT -> [Int] -> BT
unload t []     = t
unload t (x:xs) = delete (unload t xs) x

sort :: [Int] -> [Int]
sort = inorder . (load empty)

isBalanced L = True
isBalanced (N _ t u) = isBalanced t && isBalanced u && abs (balFactor t u) < 2


