module If where

-- what's a reasonable type to give to `if_` so that we can verify `bog` ? 

{-@ type TT = {v: Bool |     (Prop v)} @-}
{-@ type FF = {v: Bool | not (Prop v)} @-}


{-@ if_  :: b:Bool -> x:a -> y:a -> a @-}
if_ :: Bool -> a -> a -> a
if_ True  x _ = x
if_ False _ y = y


{-@ bog :: Nat @-}
bog :: Int
bog =
  let b  = (0 < 1)      -- :: TT
      xs = [1 ,  2,  3] -- :: [Nat]
      ys = [-1, -2, -3] -- :: [Int]
      zs = if_ b xs ys  -- :: [Nat] 
  in 
      case xs of
        h:_ -> h 
        _   -> 0


