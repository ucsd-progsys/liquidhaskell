module ParsingErrorWoes where
  
{-@ measure vsize :: a -> Int                                   @-}
{-@ type AOkIdx X          = {v:Nat | (OkRng v X (-1))}         @-}
{-@ predicate InRng V L U  = (L <= V && V <= U)                 @-}
{-@ predicate OkRng V X N  = (InRng V 0 ((vsize X) - (N + 1)))  @-}

foo :: Int
foo = 0
