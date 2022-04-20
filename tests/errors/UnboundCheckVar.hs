{-@ LIQUID "--checks=ink" @-}

module UnboundCheckVar where

inc :: Int -> Int 
inc x = x + 1

