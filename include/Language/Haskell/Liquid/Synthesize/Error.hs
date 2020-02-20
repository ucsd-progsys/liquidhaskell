module Language.Haskell.Liquid.Synthesize.Error where 

{-@ err :: { v: Int | false } -> a @-}
err :: Int -> a
err s = undefined