{-@ assume errorWithoutStackTrace :: {i:String | false } -> a @-} 
{-@ LIQUID "--eliminate=none" @-}


{-@ transpose           :: [[a]] -> {o:[[a]] | ?? } @-}
transpose               :: [[a]] -> [[a]]
transpose []             = []
transpose ([]   : xss)   = transpose xss
transpose ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (xs : [ t | (_:t) <- xss])
