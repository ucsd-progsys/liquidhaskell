
-- https://github.com/ucsd-progsys/liquidhaskell/issues/1382

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

{- 
$ stack exec -- liquid Lists.hs --checks=lemma_app_assoc0
Time (0.37s) for action ["Lists.lemma_app_assoc0"]

$ stack exec -- liquid Lists.hs --checks=lemma_app_assoc1
Time (0.23s) for action ["Lists.lemma_app_assoc1"]

$ stack exec -- liquid Lists.hs --checks=lemma_app_assoc2
Time (1.60s) for action ["Lists.lemma_app_assoc2"]
-}

module Lists where 

import Prelude hiding ((++))
import Language.Haskell.Liquid.ProofCombinators 

{-@ infixr ++  @-}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a] 
[]     ++ ys = ys 
(x:xs) ++ ys = x : (xs ++ ys)

-------------------------------------------------------------------------------

-- Full equational proof 

{-@ lemma_app_assoc0 :: xs:_ -> ys:_ -> zs:_ -> 
      { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-} 
lemma_app_assoc0 :: [a] -> [a] -> [a] -> () 
lemma_app_assoc0 []     ys zs 
  =   ([] ++ ys) ++ zs 
  === ys ++ zs 
  === [] ++ (ys ++ zs)
  *** QED 

lemma_app_assoc0 (x:xs) ys zs 
  =   ((x:xs) ++ ys) ++ zs 
  === (x: (xs ++ ys)) ++ zs 
  === x : ((xs ++ ys) ++ zs) 
    ? lemma_app_assoc0 xs ys zs
  === x : (xs ++ (ys ++ zs))
  === (x : xs) ++ (ys ++ zs)
  *** QED 

-------------------------------------------------------------------------------
-- Short PLE proof 

{-@ ple lemma_app_assoc1 @-}
{-@ lemma_app_assoc1 :: xs:_ -> ys:_ -> zs:_ -> 
      { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-} 
lemma_app_assoc1 :: [a] -> [a] -> [a] -> () 
lemma_app_assoc1 []     ys zs = () 
lemma_app_assoc1 (x:xs) ys zs = lemma_app_assoc1 xs ys zs

-------------------------------------------------------------------------------
-- Running PLE on equational proof

{-@ ple lemma_app_assoc2 @-}
{-@ lemma_app_assoc2 :: xs:_ -> ys:_ -> zs:_ -> 
      { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-} 
lemma_app_assoc2 :: [a] -> [a] -> [a] -> () 
lemma_app_assoc2 []     ys zs 
  =   ([] ++ ys) ++ zs 
  === ys ++ zs 
  === [] ++ (ys ++ zs)
  *** QED 

lemma_app_assoc2 (x:xs) ys zs 
  =   ((x:xs) ++ ys) ++ zs 
  === (x: (xs ++ ys)) ++ zs 
  === x : ((xs ++ ys) ++ zs) 
    ? lemma_app_assoc2 xs ys zs
  === x : (xs ++ (ys ++ zs))
  === (x : xs) ++ (ys ++ zs)
  *** QED 

{- 

Here is the ANF version of the proof

Lists.lemma_app_assoc2
   = \ (@ a) (ds_d2zM :: [a]) (ys :: [a]) (zs :: [a]) ->
       case ds_d2zM of lq_anf$##7205759403792803514 {
         [] ->
           let { a0 = GHC.Types.[] } in
           let { a1 = Lists.++ a0 ys } in
           let { a2 = Lists.++ a1 zs } in
           let { a3 = Lists.++ ys zs } in
           let { a4 = (===) @ [a] a2 a3 } in
           let { a5 = GHC.Types.[] } in
           let { a6 = Lists.++ ys zs } in
           let { a7 = Lists.++ a5  a6 } in
           let { a8 = (===) a4 a7 } in
             (***) a8 QED;


         : x xs ->
           let {
             lq_anf$##7205759403792803524 :: [a]
             [LclId]
             lq_anf$##7205759403792803524 = GHC.Types.: @ a x xs } in
           let {
             lq_anf$##7205759403792803525 :: [a]
             [LclId]
             lq_anf$##7205759403792803525
               = Lists.++
                   @ a (break<11>(x,xs) lq_anf$##7205759403792803524) ys } in
           let {
             lq_anf$##7205759403792803526 :: [a]
             [LclId]
             lq_anf$##7205759403792803526
               = Lists.++
                   @ a
                   (scc<CAF> scc<CAF> break<12>(x,ys,xs) lq_anf$##7205759403792803525)
                   zs } in
           let {
             lq_anf$##7205759403792803527 :: [a]
             [LclId]
             lq_anf$##7205759403792803527 = Lists.++ @ a xs ys } in
           let {
             lq_anf$##7205759403792803528 :: [a]
             [LclId]
             lq_anf$##7205759403792803528
               = GHC.Types.:
                   @ a
                   x
                   (scc<CAF>
                    scc<CAF>
                    scc<CAF>
                    scc<CAF> break<14>(ys,xs) lq_anf$##7205759403792803527) } in
           let {
             lq_anf$##7205759403792803529 :: [a]
             [LclId]
             lq_anf$##7205759403792803529
               = Lists.++
                   @ a (break<15>(x,ys,xs) lq_anf$##7205759403792803528) zs } in
           let {
             lq_anf$##7205759403792803530 :: [a]
             [LclId]
             lq_anf$##7205759403792803530
               = Language.Haskell.Liquid.ProofCombinators.===
                   @ [a]
                   (scc<CAF> break<13>(x,ys,xs,zs) lq_anf$##7205759403792803526)
                   (scc<CAF> break<16>(x,ys,xs,zs) lq_anf$##7205759403792803529) } in
           let {
             lq_anf$##7205759403792803531 :: [a]
             [LclId]
             lq_anf$##7205759403792803531 = Lists.++ @ a xs ys } in
           let {
             lq_anf$##7205759403792803532 :: [a]
             [LclId]
             lq_anf$##7205759403792803532
               = Lists.++
                   @ a
                   (scc<CAF> scc<CAF> break<18>(ys,xs) lq_anf$##7205759403792803531)
                   zs } in
           let {
             lq_anf$##7205759403792803533 :: [a]
             [LclId]
             lq_anf$##7205759403792803533
               = GHC.Types.:
                   @ a
                   x
                   (scc<CAF>
                    scc<CAF>
                    scc<CAF> break<19>(ys,xs,zs) lq_anf$##7205759403792803532) } in
           let {
             lq_anf$##7205759403792803534 :: [a]
             [LclId]
             lq_anf$##7205759403792803534
               = Language.Haskell.Liquid.ProofCombinators.===
                   @ [a]
                   (scc<CAF> break<17>(x,ys,xs,zs) lq_anf$##7205759403792803530)
                   (break<20>(x,ys,xs,zs) lq_anf$##7205759403792803533) } in
           let {
             lq_anf$##7205759403792803535 :: ()
             [LclId]
             lq_anf$##7205759403792803535
               = (scc<CAF> (scc<CAF> Lists.lemma_app_assoc2 @ a xs) ys) zs } in
           let {
             lq_anf$##7205759403792803536 :: [a]
             [LclId]
             lq_anf$##7205759403792803536
               = Language.Haskell.Liquid.ProofCombinators.?
                   @ [a]
                   (scc<CAF> break<21>(x,ys,xs,zs) lq_anf$##7205759403792803534)
                   (scc<CAF> break<22>(ys,xs,zs) lq_anf$##7205759403792803535) } in
           let {
             lq_anf$##7205759403792803537 :: [a]
             [LclId]
             lq_anf$##7205759403792803537 = Lists.++ @ a ys zs } in
           let {
             lq_anf$##7205759403792803538 :: [a]
             [LclId]
             lq_anf$##7205759403792803538
               = Lists.++
                   @ a
                   xs
                   (scc<CAF>
                    scc<CAF> break<24>(ys,zs) lq_anf$##7205759403792803537) } in
           let {
             lq_anf$##7205759403792803539 :: [a]
             [LclId]
             lq_anf$##7205759403792803539
               = GHC.Types.:
                   @ a
                   x
                   (scc<CAF>
                    scc<CAF>
                    scc<CAF> break<25>(ys,xs,zs) lq_anf$##7205759403792803538) } in
           let {
             lq_anf$##7205759403792803540 :: [a]
             [LclId]
             lq_anf$##7205759403792803540
               = Language.Haskell.Liquid.ProofCombinators.===
                   @ [a]
                   (scc<CAF> break<23>(x,ys,xs,zs) lq_anf$##7205759403792803536)
                   (break<26>(x,ys,xs,zs) lq_anf$##7205759403792803539) } in
           let {
             lq_anf$##7205759403792803541 :: [a]
             [LclId]
             lq_anf$##7205759403792803541 = GHC.Types.: @ a x xs } in
           let {
             lq_anf$##7205759403792803542 :: [a]
             [LclId]
             lq_anf$##7205759403792803542 = Lists.++ @ a ys zs } in
           let {
             lq_anf$##7205759403792803543 :: [a]
             [LclId]
             lq_anf$##7205759403792803543
               = Lists.++
                   @ a
                   (break<28>(x,xs) lq_anf$##7205759403792803541)
                   (scc<CAF>
                    scc<CAF> break<29>(ys,zs) lq_anf$##7205759403792803542) } in
           let {
             lq_anf$##7205759403792803544 :: [a]
             [LclId]
             lq_anf$##7205759403792803544
               = Language.Haskell.Liquid.ProofCombinators.===
                   @ [a]
                   (scc<CAF> break<27>(x,ys,xs,zs) lq_anf$##7205759403792803540)
                   (scc<CAF> break<30>(x,ys,xs,zs) lq_anf$##7205759403792803543) } in
           scc<CAF>
           scc<CAF>
           break<32>(x,ys,xs,zs)
           Language.Haskell.Liquid.ProofCombinators.***
             @ [a]
             (scc<CAF> break<31>(x,ys,xs,zs) lq_anf$##7205759403792803544)
             Language.Haskell.Liquid.ProofCombinators.QED
       };,
       

 -}

