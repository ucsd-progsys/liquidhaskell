{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

{-@ data List [llen] = Nil | Cons {lTl :: List} @-}
data List = Nil | Cons List

{-@ measure llen @-}
{-@ llen :: List -> Nat @-}
llen :: List -> Int
llen Nil      = 0
llen (Cons t) = 1 + llen t

{-@ reflect sz @-}
{-@ sz :: List -> Nat @-}
sz :: List -> Int
sz Nil      = 0
sz (Cons t) = 1 + sz t

-- THIS IS OK
{-@ ok :: { llen ((Cons Nil)) == 1 } @-}
ok = ()

-- THIS IS NOT
{-@ fails :: { sz (Cons Nil) == 1 } @-}
fails = ()
 
