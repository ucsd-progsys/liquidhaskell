{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}

module AbstractRefinements (
    listMax
  , insertSort
  , insertSort'
  , insertSort''
  , insertSort'''
  ) where

import Data.Set hiding (insert, foldr,size,filter, append) 
import Prelude hiding (map, foldr, filter, append)

listMax     :: [Int] -> Int

-----------------------------------------------------------------------
-- | 0. Abstract Refinements 
-----------------------------------------------------------------------

{-@ listMax :: forall <p :: Int -> Prop>. {v:[Int<p>] | len v > 0} -> Int<p> @-} 
listMax xs  = foldr1 max xs 


-- Lets define a few different subsets of Int

{-@ type Even = {v:Int | v mod 2 == 0}      @-}
{-@ type Odd  = {v:Int | v mod 2 /= 0}      @-}
{-@ type RGB  = {v:Int | 0 <= v && v < 256} @-}



{-@ xE :: Even @-}
xE = listMax [0, 200, 4000, 60] 


{-@ xO :: Odd @-}
xO = listMax [1, 21, 4001, 961] 


{-@ xR :: RGB @-}
xR = listMax [1, 21, 41, 61] 



-----------------------------------------------------------------------
-- | 1. Abstract Refinement from List's Type 
-----------------------------------------------------------------------



{-@ data List a <p :: a -> a -> Prop> 
     = N | C {x :: a, xs :: List<p> a<p x>} @-}



-----------------------------------------------------------------------
-- | 2. Instantiating Abstract Refinements 
-----------------------------------------------------------------------




{-@ type IncrList a = List <{\x y -> x <= y}> a @-} 
{-@ type DecrList a = List <{\x y -> x >= y}> a @-} 
{-@ type DiffList a = List <{\x y -> x /= y}> a @-} 

{-@ ups   :: IncrList Integer @-}
ups       = 1 `C` 2 `C` 4 `C` N

{-@ downs :: DecrList Integer @-}
downs     = 100 `C` 20 `C` 4 `C` N

{-@ diffs :: DiffList Integer @-}
diffs     = 100 `C` 1000 `C` 10 `C` 1 `C`  N



-----------------------------------------------------------------------
-- | 3. Insertion Sort: Revisited
-----------------------------------------------------------------------

{-@ insert         :: x:_ -> xs:_ -> {v:_ | AddElt v x xs && size v = 1 + size xs} @-}
insert x N         = x `C` N
insert x (C y ys)
  | x <= y         = x `C` y `C` ys
  | otherwise      = y `C` insert x ys 



{-@ insertSort      :: xs:List a -> {v:IncrList a | size v = size xs} @-}
insertSort N        = N
insertSort (C x xs) = insert x (insertSort xs)



-----------------------------------------------------------------------
-- | 3. Insertion Sort: using a `foldr` 
-----------------------------------------------------------------------



{-@ insertSort' :: xs:List a -> IncrList a @-}
insertSort' xs = foldr insert N xs




-----------------------------------------------------------------------
-- | 4. But, there are limits...
-----------------------------------------------------------------------

-- but why is this not ok?

{-@ insertSort'' :: xs:List a -> {v:IncrList a | EqSize v xs && EqElem v xs} @-}
insertSort'' xs   = foldr insert N xs


-- Hmm. Thats a bummer... How do we type `foldr` to verify the above?


-----------------------------------------------------------------------
-- | 5. Induction, as an Abstract Refinement 
-----------------------------------------------------------------------


{-@ ifoldr :: forall a b <p :: List a -> b -> Prop>. 
                 (xs:_ -> x:_ -> b<p xs> -> b<p(C x xs)>) 
               -> b<p N> 
               -> ys:List a
               -> b<p ys>                            @-}
ifoldr :: (List a -> a -> b -> b) -> b -> List a -> b
ifoldr f b N        = b
ifoldr f b (C x xs) = f xs x (ifoldr f b xs)


{-@ insertSort''' :: xs:List a -> {v:IncrList a | EqSize v xs && EqElem v xs} @-}
insertSort''' xs = ifoldr (id (\_ -> insert)) N xs

{-@ append :: xs:List a -> ys:List a -> {v:List a | UnElems v xs ys} @-} 
append xs ys = ifoldr (\_ -> C) ys xs 

{-@ filter :: (a -> Bool) -> xs:List a -> {v:List a | SubElems v xs } @-} 
filter f xs = ifoldr (id (\_ x ys -> if f x then C x ys else ys)) N xs
   
-----------------------------------------------------------------------
-- | Old definitions from 00_Refinements.hs
-----------------------------------------------------------------------

data List a = N | C a (List a)

infixr 9 `C`

{-@ measure size @-}
size          :: List a -> Int
size (C x xs) = 1 + size xs 
size N        = 0

foldr f acc N        = acc
foldr f acc (C x xs) = f x (foldr f acc xs)


{-@ predicate EqSize X Y      = size X  = size Y                      @-}
{-@ predicate EqElem X Y      = elems X = elems Y                     @-}
{-@ predicate UnElems X Y Z   = elems X = Set_cup (elems Y) (elems Z) @-}
{-@ predicate SubElems X Y    = Set_sub (elems X) (elems Y)           @-}
{-@ predicate SubConsElems X Y Ys = Set_sub (elems X) (Set_cup (Set_sng Y) (elems Ys)) @-}


{-@ qual1  :: y:_ -> ys:_ -> {v:_ | SubConsElems v y ys} @-}
qual1 :: a -> List a -> List a 
qual1 y ys = undefined 

{-@ qual2  :: y:_ -> ys:_ -> {v:_ | size v <= 1 + size ys} @-}
qual2 :: a -> List a -> List a 
qual2 y ys = undefined 



{-@ predicate AddElt V X Xs = elems V = Set_cup (Set_sng X) (elems Xs) @-}
 
{-@ measure elems ::List a -> (Set a)
    elems (N)      = (Set_empty 0)
    elems (C x xs) = (Set_cup (Set_sng x) (elems xs))
  @-}
