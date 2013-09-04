{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP,  MagicHash #-}
{-# OPTIONS_HADDOCK hide #-}

module PrimInt where


{-@ assert mtake  :: n: {v: Int | 0 <= v} 
                  -> {v:[a] | ((n > 0) <=> ((len v) > 0))} 
                  -> {v:[a] | (len(v) = n)} @-}
mtake          :: Int -> [a] -> [a]
mtake 0 _      = []
mtake n (x:xs) = x : mtake (n - 1) xs



















