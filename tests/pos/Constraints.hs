module Compose where




{-@ 
cmp :: forall < pref :: b -> Prop, postf :: b -> c -> Prop
              , pre  :: a -> Prop, postg :: a -> b -> Prop
              , post :: a -> c -> Prop
              >. 
       {w:b<postg x> -> c<postf w> -> c<post x>}
       {b<postg x> -> b<pref>}
       f:(y:b<pref> -> c<postf y>)
    -> g:(z:a<pre > -> b<postg z>)
    -> x: a<pre> -> c<post x>
@-}

cmp :: (b -> c)
    -> (a -> b)
    ->  a -> c

cmp f g x = f (g x)    