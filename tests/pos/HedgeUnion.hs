module Map () where

import Language.Haskell.Liquid.Prelude

{-@
  data Map [mlen] k a <l :: root:k -> k -> Prop, r :: root:k -> k -> Prop>
      = Tip 
      | Bin (right :: Map <l, r> (k <r key>) a) 
  @-}

{-@ measure mlen :: (Map k a) -> Int 
    mlen(Tip) = 0
    mlen(Bin r) = 1 + (mlen r)
  @-}

{-@ invariant {v:Map k a | (mlen v) >= 0}@-}

{- type OMap k a = Map <{\root v -> v < root }, {\root v -> v > root}> k a @-}

data Map k a = Tip
             | Bin (Map k a)

type Size    = Int

-- Internal representation of hedgeUnion:

{-@ LAZYVAR d20r @-}

g t1 d20i = 
  case d20i of
   Tip -> Tip
   Bin d20G -> (\_ -> let d20r = \_ -> let d20n  = \_ -> case t1 of
                                                         Tip -> liquidError ""
                                                         Bin  r -> r
                                      in case d20i of
                                          Tip -> d20n ""
                                          Bin d20j -> case d20j of
                                                        Tip -> Tip
                                                        Bin _ -> d20n ""
                         in case t1 of
                             Tip -> case d20i of 
                                      Tip -> d20r ""
                                      Bin r -> r
                             Bin _ -> d20r "") ""

-- hedgeUnion t1 Tip      = Tip  
-- hedgeUnion Tip (Bin r) = r
-- hedgeUnion t1  (Bin Tip) = Tip
-- hedgeUnion (Bin r) t = r
