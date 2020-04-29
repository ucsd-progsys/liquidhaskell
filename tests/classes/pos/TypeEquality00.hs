{-  see [NOTE:type-equality-hack] TODO-REBARE-EQ-REPR: GHC shifts the representation of the ~ to something new with 8.4.3 maybe?

 /Users/rjhala/research/liquidhaskell/tests/pos/T1295b.hs:10:5-29: Error: Illegal type specification for `constructor Main.PersonNums`
  
 10 |   = typ ~ [Int] => PersonNums
          ^^^^^^^^^^^^^^^^^^^^^^^^^
  
     constructor Main.PersonNums :: forall a##xo .
                                    (~<[]> (TYPE LiftedRep) a##xo [Int]) =>
                                    (EntityFieldPerson {VV : a##xo | len VV > 0})
     Sort Error in Refinement: {VV : typ##arY | len VV > 0}
     Cannot unify typ##arY with (@(42) @(43)) in expression: len VV << ceq2 >>

  -} 

{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeFamilies     #-}

module TypeEquality00 where

{-@ LIQUID "--exact-data-con" @-}

{-@ data EntityFieldPerson typ where                                                                                     
      PersonNums :: EntityFieldPerson {v:_ | len v > 0}                                                               
  @-}
data EntityFieldPerson typ
  = typ ~ [Int] => PersonNums

