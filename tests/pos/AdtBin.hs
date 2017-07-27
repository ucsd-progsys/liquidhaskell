module AdtBin where

data Bin = B0 | B1

{-@ inductive Bin :: Int -> Prop where
      B0 :: Prop (Bin 0)
      B1 :: Prop (Bin 1)
  @-}

-- test :: n:Int -> Prop (Bin n) -> { n == 0 || n == 1 }
{-@ test :: n:Int -> {v:Bin | prop v = Bin n} -> { n == 0 || n == 1 } @-}
test :: Int -> Bin -> ()
test n B0 = ()
test n B1 = ()
