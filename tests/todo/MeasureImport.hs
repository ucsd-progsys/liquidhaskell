{-@ LIQUID "--exactdc" @-}

import AA

{-@ lazy bar @-}
{-@ bar :: Foo a b -> {v:Foo a b | isFoo v} @-}
bar :: Foo a b -> Foo a b
bar x | isFoo x 
  = x 
bar x = bar x 
