{-@ LIQUID "--typed-holes" @-}

-- Holes should not be in the environment,
-- from which we construct terms. 

{-@ stutter :: xs:[a] -> {v:[a] | 2 * len xs ==  len v} @-}
stutter x0 = 
    case x0 of 
        []        -> x0
        (x3 : x4) -> _consCase


-- The goal is to fill the hole with:
-- : x_s3 (: x_s3 (stutter x_s4))