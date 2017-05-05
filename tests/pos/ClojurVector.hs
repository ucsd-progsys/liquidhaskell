{-
https://twitter.com/BrandonBloom/status/701261641971683328
https://github.com/clojure/clojure/blob/d5708425995e8c83157ad49007ec2f8f43d8eac8/src/jvm/clojure/lang/PersistentVector.java#L148-L164
-}

{-@ LIQUID "--no-termination" @-}

module PVec (height, arrayFor) where

import Language.Haskell.Liquid.Prelude (liquidAssume)
import qualified Data.Vector as V

import Data.Bits

-- | Generalized tree with branching 32. We "store" the height in each `Node`
--   only because it is useful in the specification (each sub-tree has the same height).
--   The height is _never_ computed and so can be eliminated at run-time.

data Tree a = Leaf a
            | Node Int (V.Vector (Tree a))


-- | Specify "height" of a tree

{-@ measure height @-}
height :: Tree a -> Int
height (Leaf _)    = 0
height (Node h ls) = 1 + h

-- | Specify tree must be "balanced", each node has 32 children

{-@ data Tree a = Leaf a
                | Node { ht   :: Nat
                       , kids :: VectorN (TreeH a ht) 32
                       }
  @-}

-- | ListN is a list of a given size N

{-@ type VectorN a N     = {v:V.Vector a | vlen v = N }  @-}

-- | TreeH is a tree of given height H

{-@ type TreeH     a H = {v:Tree a | height v = H}       @-}

-- | Specify tree height is non-negative

{-@ using (Tree a) as  {v:Tree a   | 0 <= height v} @-}

-- | Nodes and Leaves are simply trees with non-zero and zero heights resp.

{-@ type NodeT a = {v:Tree a | height v > 0} @-}
{-@ type LeafT a = {v:Tree a | height v = 0} @-}


-- | Vector stores the height
data Vec a = Vec { vShift  :: Int    -- ^ height
                 , vTree   :: Tree a -- ^ actual nodes
                 }

-- | Refined type relates height of the `vTree` with `vShift`

{-@ data Vec a = Vec { vShift :: Nat
                     , vTree  :: TreeLevel a vShift
                     }
  @-}

{-@ type TreeLevel a L = {v:Tree a | L = 5 * height v} @-}

--------------------------------------------------------------------------------

arrayFor :: Int -> Vec a -> Maybe a
arrayFor i (Vec l n) = loop l n
  where

    {-@ loop :: level:Int -> TreeLevel a level -> Maybe a @-}
    loop :: Int -> Tree a -> Maybe a
    loop level node
      | level > 0 = let b      = shift i (- level) `mask` 31  -- get child index
                        node'  = getNode node b               -- get child
                        level' = level - 5                    -- next level
                    in
                        loop level' node'

      | otherwise = Just (getValue node)

-- TODO: refine types of bit-ops, currently use an "assume"

{-@ mask :: x:Int -> y:Nat -> {v:Nat | v <= y}@-}
mask :: Int -> Int -> Int
mask x y = liquidAssume (0 <= r && r <= y) r
  where
     r   = x .&. y

-- | These are the "cast" operations, except now proven safe.

{-@ getNode :: t:NodeT a -> {v:Nat | v <= 31} -> {v:Tree a | height v = height t - 1}  @-}
getNode :: Tree a -> Int -> Tree a
getNode (Node _ ts) n = ts V.! n
getNode _           _ = impossible "provably safe"

{-@ getValue :: LeafT a -> a @-}
getValue :: Tree a -> a
getValue (Leaf x) = x
getValue _        = impossible "provably safe"

{-@ impossible :: {v:String | false} -> a @-}
impossible = error
