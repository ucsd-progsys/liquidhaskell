
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--no-case-expand" @-}

module ReflectDefault where 

data Thing = A | B | C | D 

{-@ reflect foo @-}
foo :: Thing -> Int
foo A = 0 
foo D = 10
foo _ = 1 

{-@ thmOK :: {foo C == 1} @-}
thmOK = ()

