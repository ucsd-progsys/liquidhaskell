{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeFamilies     #-}

{-@ LIQUID "--exact-data-con" @-}

{-@ data EntityFieldPerson typ where                                                                                     
      PersonNums :: EntityFieldPerson {v:_ | len v > 0}                                                               
  @-}
data EntityFieldPerson typ
  = typ ~ [Int] => PersonNums

