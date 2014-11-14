{-@ LIQUID "--no-termination"   @-}

module Foo where

import Language.Haskell.Liquid.Prelude
import Data.Set (Set (..))

data RBTree a = Leaf | Node Color a !(RBTree a) !(RBTree a)
data Color    = B | R deriving (Eq)

{-@ rbalBAD, rbalOK :: k:_ -> l:_ -> r:_ -> {v:_ | Join v k l r} @-}
rbalBAD x l r = case r of
  Node R y b (Node R z c d) -> error "ASD" -- Node R y (Node B x l b) (Node B z c d)
  Node R z (Node R y b c) d -> Node R y (Node B x l b) (Node B z c d)

rbalOK x l r = case r of
  -- Node R y b (Node R z c d) -> Node R y (Node B x l b) (Node B z c d)
  Node R z (Node R y b c) d -> Node R y (Node B x l b) (Node B z c d)

{-@ measure elems :: RBTree a -> (Set a)
    elems (Leaf)         = (Set_empty 0)
    elems (Node c k l r) = (Set_cup (Set_sng k) (Set_cup (elems l) (elems r))) 
  @-}

{-@ predicate Union V L R  = elems V = Set_cup (elems L) (elems R)                       @-}
{-@ predicate Join V X L R = elems V = Set_cup (Set_sng X) (Set_cup (elems L) (elems R)) @-}
