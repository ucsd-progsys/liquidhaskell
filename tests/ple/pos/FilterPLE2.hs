{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--etabeta"        @-}

{- | In contrast with 'FilterPLE', this test uses prelude's 'filter'
to check that PLE is able to surface it's postcondition
when lifted using distinct mechanisms.
-}
module FilterPLE2 where

{-@ data Letter = A | B | C @-}
data Letter = A | B | C

{-@ reflect isA @-}
isA :: Letter -> Bool
isA A = True
isA _ = False

{-@ inline isB @-}
isB :: Letter -> Bool
isB B = True
isB _ = False

{-@ measure isC @-}
isC :: Letter -> Bool
isC C = True
isC _ = False

{-@ as :: [Letter] -> [{v:Letter | v == A}] @-}
as :: [Letter] -> [Letter]
as = filter isA

{-@ bs :: [Letter] -> [{v:Letter | v == B}] @-}
bs :: [Letter] -> [Letter]
bs = filter isB

{-@ cs :: [Letter] -> [{v:Letter | v == C}] @-}
cs :: [Letter] -> [Letter]
cs = filter isC
