module FunSoundness where


{-@ deadfun :: {v:a | false} -> a @-}
deadfun :: a -> a
deadfun x = x

bad = deadfun f 
  where f x = x 