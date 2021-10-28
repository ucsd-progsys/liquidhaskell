-- Rewrite an app argument
{-# LANGUAGE Rank2Types #-}

{-@ LIQUID "--extensionality" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--rw-termination-check" @-}

module ReWrite8 where

import Prelude hiding (and)

data MonadPlus m = MonadPlus {
    monad  :: OurMonad m
  , zero   :: forall a. m a
  , choose :: forall a. m a -> m a -> m a
}

{-@ data MonadPlus m = MonadPlus {
        monad  :: OurMonad m
      , zero   :: forall a. m a
      , choose :: forall a. m a -> m a -> m a
    }
  @-}

{-@ reflect mmonad @-}
{-@ mmonad :: mp : MonadPlus m -> {v : OurMonad m | v = mmonad mp }@-}
mmonad = monad

data OurMonad m = OurMonad {
  bind   :: forall a b. m a -> (a -> m b) -> m b,
  mreturn :: forall a.   a -> m a
}

{-@ data OurMonad m = OurMonad {
      bind   :: forall a b. m a -> (a -> m b) -> m b,
      mreturn :: forall a.   a -> m a
    } 
  @-}



{-@ reflect mbind @-}
{-@ mbind ::
     om : OurMonad m
     -> x  : m a
     -> f  : (a -> m b)
     -> {v : m b | v == mbind om x f } @-}
mbind :: OurMonad m -> m a -> (a -> m b) -> m b
mbind (OurMonad b _) = b

{-@ guard :: mp : MonadPlus m -> p : Bool -> {v : m () | v = guard mp p } @-}
{-@ reflect guard @-}
guard :: MonadPlus m -> Bool -> m ()
guard m True  = mreturn (mmonad m) ()
guard m False = zero m

{-@ reflect mseq @-}
{-@ mseq :: om : OurMonad m
      -> ma : m a
      -> mb : m b
      -> {v : m b | v = mbind om ma (const' mb) } @-}
mseq :: OurMonad m -> m a -> m b -> m b
mseq om ma mb = mbind om ma (const' mb)

{-@ reflect const' @-}
{-@ const' :: x : a -> y : b -> {v: a | v = x} @-}
const' x _ = x

{-@ assume guardSeq ::
         mp : MonadPlus m
      -> p  : Bool
      -> q  : Bool
      -> {v : () | guard mp (and p q)
                 = mseq (mmonad mp) (guard mp p) (guard mp q) }
@-}
guardSeq :: MonadPlus m -> Bool -> Bool -> ()
guardSeq _ _ _ = ()

{-@ reflect and @-}
{-@ and :: x : Bool -> y : Bool -> {z : Bool | z <=> x && y } @-}
and :: Bool -> Bool -> Bool
and True  y = y
and False _ = False

{-@ reflect step4Lambda @-}
step4Lambda mp p x (ys, zs) =
    mseq (mmonad mp)
    (guard mp (and (x <= p) True))
    (mreturn (mmonad mp) (x:ys, zs))

{-@ reflect step5Lambda @-}
step5Lambda mp p x (ys, zs) =
    mseq (mmonad mp)
      (mseq (mmonad mp) (guard mp (x <= p)) (guard mp True) )
      (mreturn (mmonad mp) (x:ys, zs))
    
{-@ rewriteWith step4LambdaEqStep5Lambda [guardSeq] @-}
{-@ step4LambdaEqStep5Lambda ::
         mp : MonadPlus m
      ->  p : Int
      ->  x : Int
      -> tupl : ([Int], [Int])
      ->{ v : () |
       step4Lambda mp p x tupl =
       step5Lambda mp p x tupl
      }
@-}
step4LambdaEqStep5Lambda :: MonadPlus m -> Int -> Int -> ([Int], [Int]) -> ()
step4LambdaEqStep5Lambda mp p x (ys, zs) = ()
