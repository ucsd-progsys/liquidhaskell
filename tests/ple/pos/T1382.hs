
-- https://github.com/ucsd-progsys/liquidhaskell/issues/1382

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-} 

{- 
$ stack exec -- liquid Lists.hs --checks=lemma_app_assoc0
Time (0.37s) for action ["Lists.lemma_app_assoc0"]

$ stack exec -- liquid Lists.hs --checks=lemma_app_assoc1
Time (0.23s) for action ["Lists.lemma_app_assoc1"]

$ stack exec -- liquid Lists.hs --checks=lemma_app_assoc2
Time (1.60s) for action ["Lists.lemma_app_assoc2"]
-}

module T1382 where

import Prelude hiding ((++))
import Language.Haskell.Liquid.ProofCombinators 

data List a = Nil | Cons a (List a)

{-@ infixr ++  @-}
{-@ reflect ++ @-}
(++) :: List a -> List a -> List a 
Nil         ++ ys = ys 
(Cons x xs) ++ ys = Cons x (xs ++ ys)

-------------------------------------------------------------------------------

-- Full equational proof 

{-@ lemma_app_assoc0 :: xs:_ -> ys:_ -> zs:_ -> 
      { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-} 
lemma_app_assoc0 :: List a -> List a -> List a -> () 
lemma_app_assoc0 Nil     ys zs 
  =   (Nil ++ ys) ++ zs 
  === ys ++ zs 
  === Nil ++ (ys ++ zs)
  *** QED 

lemma_app_assoc0 (Cons x xs) ys zs 
  =   ((Cons x xs) ++ ys) ++ zs 
  === (Cons x (xs ++ ys)) ++ zs 
  === Cons x ((xs ++ ys) ++ zs) 
    ? lemma_app_assoc0 xs ys zs
  === Cons x (xs ++ (ys ++ zs))
  === (Cons x xs) ++ (ys ++ zs)
  *** QED 

-------------------------------------------------------------------------------
-- Short PLE proof 

{-@ ple lemma_app_assoc1 @-}
{-@ lemma_app_assoc1 :: xs:_ -> ys:_ -> zs:_ -> 
      { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-} 
lemma_app_assoc1 :: List a -> List a -> List a -> () 
lemma_app_assoc1 Nil         ys zs = () 
lemma_app_assoc1 (Cons x xs) ys zs = lemma_app_assoc1 xs ys zs

-------------------------------------------------------------------------------
-- Running PLE on equational proof

{-@ ple lemma_app_assoc2 @-}
{-@ lemma_app_assoc2 :: xs:_ -> ys:_ -> zs:_ -> 
      { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-} 
lemma_app_assoc2 :: List a -> List a -> List a -> () 
lemma_app_assoc2 Nil     ys zs 
  =   (Nil ++ ys) ++ zs 
  === ys ++ zs 
  === Nil ++ (ys ++ zs)
  *** QED 

lemma_app_assoc2 (Cons x xs) ys zs 
  =   ((Cons x xs) ++ ys) ++ zs 
  === (Cons x (xs ++ ys)) ++ zs 
  === Cons x ((xs ++ ys) ++ zs) 
    ? lemma_app_assoc2 xs ys zs
  === Cons x (xs ++ (ys ++ zs))
  === (Cons x xs) ++ (ys ++ zs)
  *** QED 


{-@ foo :: forall a b <pa :: a -> Bool, pb :: b -> Bool>. a<pa> -> b<pb> -> a<pa> @-}
foo :: a -> b -> a 
foo = undefined

infixl 3 ???

{-@ (???) :: forall a b <pa :: a -> Bool, pb :: b -> Bool>. a<pa> -> b<pb> -> a<pa> @-}
(???) :: a -> b -> a 
x ??? _ = x 
{-# INLINE (???)   #-} 



{- 

Here is the ANF-ed code that LH sees: 

Lists.lemma_app_assoc2
   = \ (@ a) (ds_d2zM :: [a]) (ys :: [a]) (zs :: [a]) ->
       case ds_d2zM of lq_anf$##7205759403792803514 {
         [] ->
           let { a0 = GHC.Types.[]    } in
           let { a1 = Lists.++ a0 ys  } in
           let { a2 = Lists.++ a1 zs  } in
           let { a3 = Lists.++ ys zs  } in
           let { a4 = (===) a2 a3     } in   -- <<< 
           let { a5 = GHC.Types.[]    } in
           let { a6 = Lists.++ ys zs  } in
           let { a7 = Lists.++ a5  a6 } in   -- <<< 
           let { a8 = (===) a4 a7     } in
             (***) a8 QED;

         : x xs ->
           let { a0 = GHC.Types.:  x xs } in
           let { a1 = Lists.++    a0 ys } in
           let { a2 = Lists.++    a1 zs } in
           let { a3 = Lists.++    xs ys } in
           let { a4 = GHC.Types.: x  a3 } in
           let { a5 = Lists.++    a4 zs } in
           let { a6 = (===) a2 a5       } in -- <<<
           let { a7 = Lists.++    xs ys } in
           let { a8 = Lists.++    a7 zs } in
           let { a9 = GHC.Types.: x  a8 } in
           let { a10 = (===) a6 a9      } in                                        -- <<< 
           let { a11 = Lists.lemma_app_assoc2 xs ys zs } in
           let { a12 = Language.Haskell.Liquid.ProofCombinators.? a10 a11 } in
           let { a13 = Lists.++ ys zs } in
           let { a14 = Lists.++ xs a13 } in
           let { a15 = GHC.Types.: x a14 } in
           let { a16 = (ProofCombinators.===) a12 a15 } in
           let { a17 = GHC.Types.: x xs } in
           let { a18 = Lists.++ ys  zs } in
           let { a19 = Lists.++ a17 a18 } in
           let { a20 = (===) a16 a19 } in                                           -- <<<
           (***) a20 QED
       };,
 -}
