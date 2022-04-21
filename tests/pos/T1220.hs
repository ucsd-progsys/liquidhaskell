{-@ LIQUID "--exactdc" @-}

module T1220 where

{-@ unsafe :: {t : AB | not (isA t)} -> {t /= A}  @-}
unsafe :: AB -> ()
unsafe t | isA t = ()
unsafe _ = ()

{-@ safe :: {t : AB | not (isA t)} -> {not (t == A)}  @-}
safe :: AB -> ()
safe t | isA t = ()
safe _ = ()

{-@ measure isA @-}
{-@ assume isA :: AB -> Bool @-}
isA :: AB -> Bool 
isA A = True
isA B = False


data AB = A | B 
