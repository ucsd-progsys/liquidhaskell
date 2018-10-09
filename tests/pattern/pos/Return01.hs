
{-@ silly :: IO {v:Int | v = 0} @-}
silly :: IO Int
silly = return 0 

