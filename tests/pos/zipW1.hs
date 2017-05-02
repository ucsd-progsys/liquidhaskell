module Import where 
	
import Language.Haskell.Liquid.Prelude -- (safeZipWith)

{-@ foo :: (a -> b -> c) -> xs : [a] -> ys:{v:[b] | len v = len xs} 
        -> {v : [c] | len v  = len xs} @-}
foo = safeZipWith


{- safeZipWith :: (a -> b -> c) -> xs : [a] -> ys:{v:[b] | len v = len xs} 
                -> {v : [c] | len v = len xs} @-}