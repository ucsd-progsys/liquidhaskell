{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--extensionality" @-}
{-@ LIQUID "--ple" @-}
module SemigroupOp where

class YYSemigroup a where
    ymappend :: a -> a -> a
    {-@ lawAssociative :: v:a -> v':a -> v'':a -> {ymappend (ymappend v v') v'' == ymappend v (ymappend v' v'')} @-}
    lawAssociative :: a -> a -> a -> ()

data Op a = Op a

{-@ reflect mappendOp @-}
mappendOp :: (YYSemigroup a) => Op a -> Op a -> Op a
mappendOp (Op x) (Op y) = Op (ymappend y x)

{-@ lawAssociativeOp :: YYSemigroup a => v:Op a -> v':Op a -> v'':Op a -> {mappendOp (mappendOp v v') v'' == mappendOp v (mappendOp v' v'') }@-}
lawAssociativeOp :: YYSemigroup a => Op a -> Op a -> Op a -> ()
lawAssociativeOp (Op x) (Op y) (Op z) = lawAssociative z y x

{-@ mylawAssociative :: YYSemigroup a => v:a -> v':a -> v'':a -> {ymappend (ymappend v v') v'' == ymappend v (ymappend v' v'')}  @-}
mylawAssociative :: YYSemigroup a => a -> a -> a -> ()
mylawAssociative x y z = lawAssociative x y z

instance (YYSemigroup a) => YYSemigroup (Op a) where
  ymappend = mappendOp 
  lawAssociative x y z = lawAssociativeOp x y z
