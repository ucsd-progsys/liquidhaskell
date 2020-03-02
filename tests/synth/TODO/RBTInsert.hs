{-@ LIQUID "--typed-holes" @-}

module RBTInsert where

import qualified Data.Set as S
import Language.Haskell.Liquid.Synthesize.Error

{-@ type Color = { v: Int | v == 0 || v == 1 } @-}
type Color = Int

{-@ data RBT [size] a = 
    Empty 
    | Node { 
          x :: a
        , col :: Color
        , left :: { v: RBT { v: a | v < x } | col == 0 ==> color v == 1 }
        , right :: { v: RBT { v: a | x < v } | col == 0 ==> color v == 1 &&
                                           blackHeight v == blackHeight left }
      }
  @-}
data RBT a = Empty | Node a Color (RBT a) (RBT a)

{-@ measure color @-}
{-@ color :: RBT a -> Nat @-}
color :: RBT a -> Int
color Empty          = 1
color (Node x c l r) = c

{-@ measure size @-}
{-@ size :: RBT a -> Nat @-}
size :: RBT a -> Int
size Empty          = 0
size (Node x c l r) = 1 + size l + size r

{-@ measure rbtElts @-}
{-@ rbtElts :: RBT a -> S.Set a @-}
rbtElts :: Ord a => RBT a -> S.Set a
rbtElts Empty          = S.empty
rbtElts (Node x c l r) = S.union (S.union (rbtElts l) (rbtElts r)) (S.singleton x)

{-@ measure blackHeight @-}
{-@ blackHeight :: RBT a -> Nat @-}
blackHeight :: RBT a -> Int
blackHeight Empty = 0
blackHeight (Node x c l r) = c + blackHeight l

{-@ data WeakRBT [wSize] a =
          Ok {
              ox :: a
            , c :: Color
            , l :: { v: RBT { v: a | v < ox } | c == 0 ==> color v == 1 }
            , r :: { v: RBT { v: a | ox < v } | c == 0 ==> color v == 1 && 
                                               blackHeight v == blackHeight l }
        }
        | Bad {
              bx :: a
            , bc :: Color
            , bl :: { v: RBT { v: a | v < bx } | color v == bc }
            , br :: { v: RBT { v: a | bx < v } | color v /= bc && 
                                               blackHeight v == blackHeight bl } 
        }
  @-}
data WeakRBT a = Ok a Color (RBT a) (RBT a) | Bad a Color (RBT a) (RBT a)

{-@ measure wSize @-}
{-@ wSize :: WeakRBT a -> Nat @-}
wSize :: WeakRBT a -> Int
wSize (Ok x c l r) = 1 + size l + size r
wSize (Bad x c l r) = 1 + size l + size r

{-@ measure wrbtElts @-}
{-@ wrbtElts:: WeakRBT a -> S.Set a @-}
wrbtElts:: Ord a => WeakRBT a -> S.Set a
wrbtElts (Ok x c left right) = S.union (S.singleton x) (S.union (rbtElts left) (rbtElts right))
wrbtElts (Bad x lc left right) = S.union (S.singleton x) (S.union (rbtElts left) (rbtElts right))
  
{-@ measure wHeight @-}
{-@ wHeight :: WeakRBT a -> Nat @-}
wHeight :: WeakRBT a -> Int
wHeight (Ok x c left right) = c + blackHeight left
wHeight (Bad x lc left right) = blackHeight left

{-@ measure isOk @-} 
{-@ isOk :: WeakRBT a -> Bool @-}
isOk Ok{}  = True
isOk Bad{} = False
  
{-@ measure wColor @-} 
{-@ wColor :: WeakRBT a -> Color @-}
wColor (Ok x c left right)   = c
wColor (Bad x lc left right) = 0

-- leq :: x: a -> y: a -> {Bool | _v == (x <= y)}
-- neq :: x: a -> y: a -> {Bool | _v == (x != y)}  

{-@ balanceR :: x: a ->
              c: Color ->
              { l : RBT { v: a | v < x} | c == 0 ==> color l == 1 } ->
              { r: WeakRBT { v: a | v > x } | (c == 0 ==> isOk r) && 
                                              wHeight r == blackHeight l } ->
              { v: WeakRBT a | wrbtElts v == S.union (S.singleton x) (S.union (rbtElts l) (wrbtElts r)) && 
                               wHeight v == blackHeight l + c && 
                               wSize v == 1 + size l + wSize r &&
                               (isOk v || c == 0) }
  @-}
balanceR :: a -> Color -> RBT a -> WeakRBT a -> WeakRBT a
balanceR y c l r = undefined

{-@ balanceL :: y: a ->
                c: Color ->
                { l: WeakRBT { v: a | v < y} | c == 0 ==> isOk l } ->
                { r: RBT { v: a | v > y} | (c == 0 ==> color r == 1) && 
                                           blackHeight r == wHeight l } ->
                { v: WeakRBT a | wrbtElts v == S.union (S.singleton y) (S.union (rbtElts r) (wrbtElts l)) &&
                                 wHeight v == blackHeight r + c && 
                                 wSize v == 1 + wSize l + size r &&
                                 (isOk v || c == 0) }
  @-}
balanceL :: a -> Color -> WeakRBT a -> RBT a -> WeakRBT a
balanceL y c l r = undefined

{-@ ins :: x: a -> t: RBT a -> { v: WeakRBT a | wrbtElts v == S.union (S.singleton x) (rbtElts t) &&
                                                wHeight v == blackHeight t &&
                                                size t <= wSize v && 
                                                wSize v <= size t + 1 &&
                                                (isOk v || color t == 0) } 
  @-}
ins :: Ord a => a -> RBT a -> WeakRBT a
ins x t =
    case t of
      Empty -> Ok x red Empty Empty
      Node x9 x10 x11 x12 -> 
        if x == x9
          then Ok x9 x10 x11 x12
          else if x9 <= x
                    then balanceR x9 x10 x11 (ins x x12)
                    else balanceL x9 x10 (ins x x11) x12

{-@ red :: { v: Color | v == 0 } @-}
red :: Int 
red = 0

{-@ black :: { v: Color | v == 1 } @-}
black :: Int 
black = 1

{-@ mkBlack :: t: WeakRBT a -> { v: RBT a | rbtElts v == wrbtElts t} @-}
mkBlack :: WeakRBT a -> RBT a
mkBlack t = 
  case t of
    Ok x5 x6 x7 x8      -> Node x5 x6 x7 x8
    Bad x17 x18 x19 x20 -> Node x17 black x19 x20

{-@ insert :: x: a -> t: RBT a -> { v: RBT a | rbtElts v == S.union (rbtElts t) (S.singleton x) } @-}
insert :: Ord a => a -> RBT a -> RBT a
insert x t =
    case t of
      Empty -> Node x black Empty Empty
      Node x9 x10 x11 x12 -> mkBlack (ins x t)
