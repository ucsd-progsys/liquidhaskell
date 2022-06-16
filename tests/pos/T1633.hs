{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-@ LIQUID "--max-case-expand=0" @-}
{-@ LIQUID "--no-totality"       @-}

module T1633 where

import Data.Void

data Relation a b where
  Empty :: Relation Void Void
  One :: Int -> Relation () ()
  Join :: Relation c b -> Relation d b -> Relation (Either c d) b
  Fork :: Relation a c -> Relation a d -> Relation a (Either c d)
  deriving (Num)
-- Here I use a type 'Natural 0 1' but I wanted to try and refine the GADT.
{-@
data Relation a b where
  Empty :: Relation Void Void
  One :: {v:Int | v = 0 || v = 1} -> Relation () ()
  Join :: Relation c b -> Relation d b -> Relation (Either c d) b
  Fork :: Relation a c -> Relation a d -> Relation a (Either c d)
@-}

-- (Eq, Num, Ord, etc.. instances ...)

comp :: Relation b c -> Relation a b -> Relation a c
comp Empty Empty           = Empty
comp (One a) (One b)       = One (a * b)
comp (Join a b) (Fork c d) = comp a c + comp b d         -- Divide-and-conquer law
comp (Fork a b) c          = Fork (comp a c) (comp b c) -- Fork fusion law
comp c (Join a b)          = Join (comp c a) (comp c b)  -- Join fusion law
