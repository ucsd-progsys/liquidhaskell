module ElabLocation3 where
{-@ LIQUID "--expect-error-containing=ElabLocation3.hs:174:1-5" @-}
{-@ LIQUID "--reflection" @-}

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (id)

{-@ type Pos = {v:Int | 0 < v} @-}

{-@ incr :: Pos -> Pos @-}
incr :: Int -> Int
incr x = x + 2



{-@
data Monkey =
  M { number :: Nat,
      items :: [Int],
      operation :: Int -> Int,
      testMod :: {n:Int | n > 0 },
      ifTrue :: Nat,
      ifFalse :: Nat,
      count :: Nat
    }
@-}
data Monkey =
  M { number :: Int,
      items :: [Int],
      operation :: Int -> Int,
      testMod :: Int,
      ifTrue :: Int,
      ifFalse :: Int,
      count :: Int }

{-@ myCount :: _ -> Nat @-}
myCount :: Monkey -> Int 
myCount M { count = k}  = k 


showMonkey :: Monkey -> String
showMonkey (M n i o m ifT ifF count) =
  "#" ++ (show n) ++ " items " ++ (show i) ++ " examined " ++ (show count) ++ "\n"

instance Show Monkey where show = showMonkey

{-@ type MonkeyIR X = {m:Monkey | number m < X && ifTrue m < X && ifFalse m < X } @-}

-- fst = item
-- snd = destination
{-@ type MonkeyItem X = (Int, {n:Nat | n < X}) @-}

{-@ turn :: x:Int -> {worry:Int | worry /= 0 } -> {modulus:Int | modulus /= 0} -> m:MonkeyIR x -> {d:[MonkeyItem x] | len d = len (items m)} @-}
turn :: Int -> Int -> Int -> Monkey -> [(Int, Int)]
turn _ worry modulus (M _ oldItems op m dTrue dFalse _) =
  map toDestination oldItems where
  toDestination i = let newWorry = (( op i ) `div` worry) `mod` modulus in
    (newWorry, if newWorry `mod` m == 0 then dTrue else dFalse)

-- What I would like to do:
-- measure countOfItems :: [Monkey] -> Int
-- countOfItems [] = 0
-- countOfItems (m:ms) = len (items m) + countOfItems ms
--
--      -> {m2:[MonkeyIR x] | len m2 = len m && countOfItems m2 = countOfItems m + len mi} 
--
-- But this measure gets applied to all lists, which doesn't work

{-@ data MonkeyList = Empty | MCons { headMonkey :: MonkeyIR 8, barrel :: MonkeyList } @-}
data MonkeyList =
  Empty |
  MCons Monkey MonkeyList

{-@ measure mLen :: MonkeyList -> Int
      mLen Empty = 0
      mLen (MCons m ms) = 1 + mLen  ms 
  @-}

{-@ measure countOfItems :: MonkeyList -> Int
      countOfItems Empty = 0
      countOfItems (MCons m ms) = len (items m) + countOfItems ms @-}

{-
{-@ distribute2 :: m:MonkeyList -> {mi:[MonkeyItem 8] | len mi <= mLen m}
     -> {m2:MonkeyList | mLen m2 = mLen m && countOfItems m2 = countOfItems m + len mi} @-}
distribute2 :: MonkeyList -> [(Int,Int)] -> MonkeyList 
distribute2 Empty [] = Empty
distribute2 Empty _ = error "Shouldn't happen"
distribute2 (MCons m ms) destinations =
  MCons (m {items = (items m) ++ newItems}) (distribute2 ms (filter (notP toMe) destinations)) where
  newItems = map fst (filter toMe destinations)
  toMe (_,d) = d == number m
-}

{-@ distribute :: x:Int -> m:[MonkeyIR x] -> mi:[MonkeyItem x]
     -> {m2:[MonkeyIR x] | len m2 = len m} @-}
distribute :: Int -> [Monkey] -> [(Int,Int)] -> [Monkey]
distribute _ [] _ = []
distribute x (m:ms) destinations =
  (m {items = (items m) ++ newItems}):(distribute x ms destinations) where
  newItems = map fst (filter toMe destinations)
  toMe (_,d) = d == number m

-- Monkey N's turn in the round
{-@ roundN :: x:Int -> 
              {worry:Int | worry /= 0 } -> 
	      {modulus:Int | modulus /= 0} -> 
	      {before:[MonkeyIR x] | len before = x} -> 
	      {n:Nat | n < x } -> 
	      {after:[m:MonkeyIR x] | len after = x} @-}
roundN :: Int -> Int -> Int -> [Monkey] -> Int -> [Monkey]
roundN x worry modulus monkeys n =
  let m = (monkeys !! n)
      destinations = turn x worry modulus m
      newCount = (myCount m) + length (items m)
      afterRemoval = (take n monkeys) ++ [(m {items = [], count = newCount} )] ++ (drop (n+1) monkeys) in
    distribute x afterRemoval destinations

-- One round of all monkeys
-- Complicated by the need to prove termination.
{-@ round :: x:Int -> {worry:Int | worry /= 0} -> {modulus:Int | modulus /= 0 } -> 
             {before:[MonkeyIR x] | len before = x} -> 
	     {after:[MonkeyIR x] | len after = x} @-}
round :: Int -> Int -> Int -> [Monkey] -> [Monkey]
round x worry modulus monkeys = go 0 monkeys where
  {-@ go :: {n:Int | n >= 0 && n <= x} -> {m:[MonkeyIR x] | len m = x} -> {m2:[MonkeyIR x] | len m2 = x} / [ x - n ] @-}
  go n ms = if n == x then ms
    else go (n+1) (roundN x worry modulus ms n)


{-@ m0 :: MonkeyIR 4 @-}
m0 = M { number=0, items=[79,98], operation=(\o -> o * 19), testMod=23, ifTrue=2, ifFalse=3, count=0 }
{-@ m1 :: MonkeyIR 4 @-}
m1 = M { number=1, items=[54,65,75,74], operation=(\o -> o + 6), testMod=19, ifTrue=2, ifFalse=0, count=0 }
{-@ m2 :: MonkeyIR 4 @-}
m2 = M { number=2, items=[79,60,97], operation=(\o -> o * o), testMod=13, ifTrue=1, ifFalse=3, count=0 }
{-@ m3 :: MonkeyIR 4 @-}
m3 = M { number=3, items=[74], operation=(\o -> o + 3), testMod=17, ifTrue=0, ifFalse=1, count=0 }
       
{-@ example :: {m:[MonkeyIR 4] | len m = 4} @-}
example :: [Monkey]
example = [ m0, m1, m2, m3 ]

{-@ i0 :: MonkeyIR 8 @-}
i0 = M { number=0, items=[59,74,65,86], operation=(\o -> o * 19), testMod=7, ifTrue=6, ifFalse=2, count=0 }
{-@ i1 :: MonkeyIR 8 @-}
i1 = M { number=1, items=[62,84,72,91,68,78,51], operation=(\o -> o + 1), testMod=2, ifTrue=2, ifFalse=0, count=0 }
{-@ i2 :: MonkeyIR 8 @-}
i2 = M { number=2, items=[78,84,96], operation=(\o -> o + 8), testMod=19, ifTrue=6, ifFalse=5, count=0 }
{-@ i3 :: MonkeyIR 8 @-}
i3 = M { number=3, items=[97,86], operation=(\o -> o * o), testMod=3, ifTrue=1, ifFalse=0, count=0 }
{-@ i4 :: MonkeyIR 8 @-}
i4 = M { number=4, items=[50], operation=(\o -> o + 6), testMod=13, ifTrue=3, ifFalse=1, count=0 }
{-@ i5 :: MonkeyIR 8 @-}
i5 = M { number=5, items=[73,65,69,65,51], operation=(\o -> o * 17), testMod=11, ifTrue=4, ifFalse=7, count=0 }
{-@ i6 :: MonkeyIR 8 @-}
i6 = M { number=6, items=[69, 82, 97, 93, 82, 84, 58, 63], operation=(\o -> o + 5), testMod=5, ifTrue=5, ifFalse=7, count=0 }
{-@ i7 :: MonkeyIR 8 @-}
i7 = M { number=7, items=[81, 78, 82, 76, 79, 80], operation=(\o -> o + 3), testMod=17, ifTrue=3, ifFalse=4, count=0 }
       
{-@ input :: {m:[MonkeyIR 8] | len m = 8} @-}
input :: [Monkey]
input = [ i0, i1, i2, i3, i4, i5, i6, i7 ]

{-@ assume iterate :: (a -> a) -> a -> {l:[a] | len l >= 1000000 } @-}

computeModulus :: [Monkey] -> Int
computeModulus ms = foldl1 (*) (map testMod ms)


id z = z

part1 :: () -> IO ()
part1 _ = do
  putStrLn "Part 1"
  let m1 = computeModulus example in do
    putStrLn $ "Working mod " ++ show m1
    let allRounds = iterate {- (Main.round 4 3 m1) -} id example in
      print $ allRounds !! 20
    
  let m2 = computeModulus input in do
    putStrLn $ "Working mod " ++ show m2    
    let allRounds2 = iterate {- (Main.round 8 3 m2) -} id input in
      print $ allRounds2 !! 20

mymain :: IO ()
mymain = part1 ()

