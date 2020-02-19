{-# LANGUAGE RankNTypes #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--extensionality" @-}
{-@ LIQUID "--ple" @-}
module SemigroupOp where
import ProofCombinators

class YYSemigroup a where
    ymappend :: a -> a -> a
    {-@ lawAssociative :: v:a -> v':a -> v'':a -> {ymappend (ymappend v v') v'' == ymappend v (ymappend v' v'')} @-}
    lawAssociative :: a -> a -> a -> ()

data PNat = Z | S PNat



-- instance YYSemigroup PNat where
--   ymappend _ _ = Z
--   lawAssociative _ _ _ = ()

-- instance YYSemigroup PNat where
--   ymappend Z n = n
--   -- S (ymappend d m n) == S ($cmappend m n)
--   ymappend (S m) n = S (ymappend m n)
--   -- lawAssociative m n p = undefined
--   lawAssociative Z m n = ymappend Z (ymappend m n) `k`
--                          ymappend m n `k`
--                          ymappend (ymappend Z m) n `k`
--                          ()
--   lawAssociative (S p) m n = ymappend (S p) (ymappend m n) `k`
--                              S (ymappend p (ymappend m n)) `k`
--                              lawAssociative p m n `k`
--                              S (ymappend (ymappend p m) n) `k`
--                              ymappend (S (ymappend p m) ) n `k`
--                              ymappend (ymappend (S p) m ) n `k`
--                              ()


data Op a = Op a

k :: a -> b -> b
k _ y = y

instance (YYSemigroup a) => YYSemigroup (Op a) where
  ymappend (Op x) (Op y) = Op (ymappend y x)
  lawAssociative (Op x) (Op y) (Op z) = lawAssociative z y x `k` (1 =>= 3) `cast` ()

-- -- {-@ reflect mappendOp @-}
-- -- mappendOp :: (YYSemigroup a) => Op a -> Op a -> Op a
-- -- mappendOp (Op x) (Op y) = Op (ymappend y x)

-- -- {-@ lawAssociativeOp :: YYSemigroup a => v:Op a -> v':Op a -> v'':Op a -> {mappendOp (mappendOp v v') v'' == mappendOp v (mappendOp v' v'') }@-}
-- -- lawAssociativeOp :: YYSemigroup a => Op a -> Op a -> Op a -> ()
-- -- lawAssociativeOp (Op x) (Op y) (Op z) = lawAssociative z y x

-- {-@ mylawAssociative :: YYSemigroup a => v:a -> v':a -> v'':a -> {ymappend (ymappend v v') v'' == ymappend v (ymappend v' v'')}  @-}
-- mylawAssociative :: YYSemigroup a => a -> a -> a -> ()
-- mylawAssociative  = lawAssociative

