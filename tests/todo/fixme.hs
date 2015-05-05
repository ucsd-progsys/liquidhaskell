data L a = Nil

{-@ measure bar :: L Int -> Int
    bar Nil = 0
  @-}   

{-@ measure barr :: L Int -> Prop
    barr Nil = true
  @-}     