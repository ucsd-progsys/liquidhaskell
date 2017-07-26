module AdtBin where

data Bin = B0 | B1

{-@ relation BinP :: Int -> Prop @-}

{-@ inductive Bin where
      B0 :: Prop (BinP 0)
      B1 :: Prop (BinP 1)
  @-}

-- test :: n:Int -> Prop (BinP n) -> { n == 0 || n == 1 }
{-@ test :: n:Int -> {v:Bin | prop v = BinP n} -> { n == 0 || n == 1 } @-}
test :: Int -> Bin -> ()
test n B0 = ()
test n B1 = ()
