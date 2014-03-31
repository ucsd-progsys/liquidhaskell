module AVLTree where 

-- from: https://gist.github.com/gerard/109729

data BT a = L 
          | N { dep   :: !Int 
              , value :: a   
              , left  :: !(BT a)
              , right :: !(BT a) 
              }
          deriving (Show, Eq)

{-@ data BT a [dep] = L 
                    | N (dep   :: !Int) 
                        (value :: a   )
                        (left  :: Bt a) 
                        (right :: BT a) 
  @-}

-- Nice, small and useful functions
empty = L 
 
-- You could say, depth L == Nothing depth (N v L L) == Just 0, but works for
-- me better this way:
depth L = 0
depth (N d _ _ _) = d 

{-@ measure depth   :: BT a -> Int 
    depth (L)         = 0
    depth (N d x l r) = 1 + (if (depth l) <= (depth r) then (depth r) else (depth l)) 
  @-}

inorder             :: BT a -> [a]
inorder L           = []
inorder (N _ v l r) = inorder l ++ [v] ++ inorder r
 
-- left (N _ t _) = t
-- right (N _ _ u) = u
-- value (N v _ _) = v
 
btmin = head . inorder
 
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
