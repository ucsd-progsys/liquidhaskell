module Chunks where

{-@ LIQUID "--scrape-imports" @-}


{-@ type SafeChunkSize = {v:Int | 1 < v } @-}

{-@ type Pos = {v:Int | 0 < v} @-}

{-@ predicate ValidChunk V XS N 
    = if len XS == 0 
        then (len V == 0) 
        else (((1 < len XS && 1 < N) => (len V  < len XS)) 
          && ((len XS <= N ) => len V == 1))            
  @-}

{-@ chunks :: n:Pos -> xs:[a] -> {v:[[a]] | ValidChunk v xs n } / [len xs] @-}
chunks :: Int -> [a] -> [[a]]
chunks _ [] = [] 
chunks n xs = let (x, xs') = splitAt n xs in x:chunks n xs'