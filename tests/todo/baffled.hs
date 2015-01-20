{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
{- LIQUID "--diffcheck"     @-}

module AVL where

main :: IO ()
main = return ()

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

{-@ invariant {v:AVL k v | 0 <= ht v} @-}

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


{-@ predicate HtDiff S T D = (tht S) - (tht T) == D @-}

{-@ add :: k -> v -> t:AVL k v -> {v: AVL k v | (tht t - 1 <= tht v || tht t - 2 = tht v) && tht v <= tht t + 1} @-}
add k' v' t@(Node k v l r h)
  -- RJ: This case is obviously fine
  
  | k' == k     = Node k' v' l r h  

  -- RJ: Maddeningly, this case is fine too
                  
--   | k' <  k     = let mickey = fox k' v' l
--                   in
--                      bal k v mickey r   
  -- NV: This is fine
--   | k < k', height l >= height r = let mouse = fox k' v' r  in
--                                   bal k v l mouse 

  -- RJ: HEREHEREHERE this is the problem (I GIVE UP)
  -- here it might be the case that 'tht t - 2 = tht v'
     | k < k', height l < height r = let mouse = fox k' v' r  in
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

