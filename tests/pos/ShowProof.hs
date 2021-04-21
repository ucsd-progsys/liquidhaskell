{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
module ShowProof where

data N = S N | Z

{-@ infix #+ @-}
{-@ reflect #+ @-}
m #+ Z     = m
m #+ (S n) = S (m #+ n)

{-@ showProof proof @-}
{-@ proof :: { ((S Z) #+ (S Z)) == S (S Z) } @-}
proof = ()

