{-
https://twitter.com/BrandonBloom/status/701261641971683328
https://github.com/clojure/clojure/blob/d5708425995e8c83157ad49007ec2f8f43d8eac8/src/jvm/clojure/lang/PersistentVector.java#L148-L164
-}

{-@ LIQUID "--no-termination" @-}

module PVec (arrayFor, height) where

import Data.Bits

-- | Simplified binary tree

data Tree a = Leaf a
            | Node {tLeft :: (Tree a), tRight :: (Tree a) }

-- | Specify "height" of a tree

{-@ measure height @-}
height :: Tree a -> Int
height (Leaf _)   = 0
height (Node l _) = 1 + height l

-- | A tree whose height is H

{-@ type TreeH a H = {v:Tree | height v == H } @-}

-- | Specify tree must be "balanced"

{-@ data Tree a = Leaf a
                | Node { tLeft  :: Tree a
                       , tRight :: TreeH a (height tLeft) }
  @-}

-- | Specify tree height is non-negative

{-@ using (Tree a) as  {v:Tree a | 0 <= height v} @-}

-- | Vector stores the height

data Vec a = Vec { vShift  :: Int    -- ^ height
                 , vTree   :: Tree a -- ^ actual nodes
                 }

-- | Refined type relates height of the `vTree` with `vShift`

{-@ data Vec a = Vec { vShift :: Nat
                     , vTree  :: TreeH a vShift
                     }
  @-}

--------------------------------------------------------------------------------

arrayFor :: Int -> Vec a -> Maybe a
arrayFor i (Vec l n) = loop l n
  where
    loop :: Int -> Tree a -> Maybe a
    loop level node
      | level > 0 = let b      = shift i (- level) `mod` 2  -- get bit 0 or 1
                        node'  = getNode node b             -- get child
                        level' = level - 1                  -- next level
                    in
                        loop level' node'

      | otherwise = Just (getValue node)

{-@ getNode :: t:{Tree a | 0 < height t}
            -> {v:Nat | v < 2}
            -> {v:Tree a | height v = height t - 1 }
  @-}
getNode :: Tree a -> Int -> Tree a
getNode (Node l _) 0 = l
getNode (Node _ r) 1 = r
getNode _          _ = impossible "provably safe"

{-@ getValue :: {t:Tree a | 0 = height t} -> a @-}
getValue :: Tree a -> a
getValue (Leaf x) = x
getValue _        = impossible "provably safe"

{-@ impossible :: {v:String | false} -> a @-}
impossible = error
