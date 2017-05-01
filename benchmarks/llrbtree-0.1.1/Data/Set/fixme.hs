module Fixme where

import Language.Haskell.Liquid.Prelude

{-@ 
  data Splay a <l :: root:a -> a -> Bool, r :: root:a -> a -> Bool>
       = Node (value :: a) 
              (left  :: Splay <l, r> (a <l value>)) 
              (right :: Splay <l, r> (a <r value>)) 
       | Leaf 
@-}

data Splay a = Leaf | Node a (Splay a) (Splay a) deriving Show

{-@ type OSplay a = Splay <{v:a | v < root}, {v:a | v > root}> a @-}

{-@ split :: Ord a => x:a -> OSplay a
             -> (Bool, OSplay {v:a | v<x}, OSplay {v:a | v>x})
                 <{v:Splay {v:a | (~(fld) => (v!=x))} |0=0},{v:Splay a | 0=0} >
@-}

split :: Ord a => a -> Splay a -> (Bool, Splay a, Splay a)
split _ Leaf = (False,Leaf,Leaf)
split k (Node xk xl xr) = case compare k xk of
    EQ -> (True, xl, xr)
    GT -> case xr of
        Leaf -> (False, Node xk xl Leaf, Leaf)
        Node yk yl yr -> case compare k yk of
            EQ ->     (True, Node xk xl yl, yr)           -- R  :zig
            GT -> let (b, lt, gt) = split k yr            -- RR :zig zag
                  in  (b, Node yk (Node xk xl yl) lt, gt)
            LT -> let (b, lt, gt) = split k yl
                  in  (b, Node xk xl lt, Node yk gt yr)   -- RL :zig zig
    LT -> case xl of
        Leaf          -> (False, Leaf, Node xk Leaf xr)
        Node yk yl yr -> case compare k yk of
            EQ ->     (True, yl, Node xk yr xr)           -- L  :zig
            GT -> let (b, lt, gt) = split k yr            -- LR :zig zag
                  in  (b, Node yk yl lt, Node xk gt xr)
            LT -> let (b, lt, gt) = split k yl            -- LL :zig zig
                  in  (b, lt, Node yk gt (Node xk yr xr))
