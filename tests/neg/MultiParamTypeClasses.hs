{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

class Add a b where
    rAdd :: [a] -> [b] -> [a]

{-@ instance (Num k) => Add k k where 
     rAdd :: 
        x : {v : [k] | len v > 0} 
        -> {v : [k] | (len v = len x) && len v > 0} 
        -> {v : [k] | len v > 0}

@-}
instance (Num k) => Add k k where
    rAdd x y = x

main = putStrLn (show (rAdd ([] :: [Double]) ([] :: [Double])))