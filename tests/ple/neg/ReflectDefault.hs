{-@ LIQUID "--expect-any-error" @-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--max-case-expand=0" @-}

module ReflectDefault where

data Thing = A | B | C | D 

{-@ reflect foo @-}
foo :: Thing -> Int
foo A = 0 
foo D = 10
foo _ = 1 

{-@ thmOK :: {foo C == 1} @-}
thmOK = ()

{-@ thmBAD :: {foo A == 1} @-}
thmBAD = ()

