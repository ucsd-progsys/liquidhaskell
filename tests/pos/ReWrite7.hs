-- A more challenging example
{-# LANGUAGE Rank2Types #-}

{-@ LIQUID "--extensionality" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--prune-unsorted" @-}


module ReWrite7 where

data MonadPlus m = MonadPlus {
    mmonad  :: OurMonad m
  , zero   :: forall a. m a
  , choose :: forall a. m a -> m a -> m a
}

{-@ data MonadPlus m = MonadPlus {
        mmonad  :: OurMonad m
      , zero   :: forall a. m a
      , choose :: forall a. m a -> m a -> m a
    }
  @-}


data OurMonad m = OurMonad {
  bind :: forall a b. m a -> (a -> m b) -> m b,
  mreturn :: forall a.   a -> m a
}

{-@ data OurMonad m = OurMonad {
      bind   :: forall a b. m a -> (a -> m b) -> m b,
      mreturn :: forall a.   a -> m a
    } 
  @-}


{-@ reflect const' @-}
{-@ const' :: x : a -> y : b -> {v: a | v = x} @-}
const' x _ = x

{-@ reflect mbind @-}
{-@ mbind ::
         om : OurMonad m
      -> x  : m a
      -> f  : (a -> m b)
      -> {v : m b | v == mbind om x f } @-}
mbind :: OurMonad m -> m a -> (a -> m b) -> m b
mbind (OurMonad b _) = b

{-@ reflect mseq @-}
{-@ mseq :: om : OurMonad m
     -> ma : m a
     -> mb : m b
     -> {v : m b | v = mbind om ma (const' mb) } @-}
mseq :: OurMonad m -> m a -> m b -> m b
mseq om ma mb = mbind om ma (const' mb)

{-@ guard :: mp : MonadPlus m -> p : Bool -> {v : m () | v = guard mp p } @-}
{-@ reflect guard @-}
guard :: MonadPlus m -> Bool -> m ()
guard m True  = mreturn (mmonad m) ()
guard m False = zero m

{-@ reflect filt @-}
filt :: MonadPlus m -> (a -> Bool) -> a -> m a
filt mp p x = mseq (mmonad mp) (guard mp (p x)) (mreturn (mmonad mp) x)

{-@ reflect lhs @-}
lhs :: MonadPlus m -> Int -> Int -> ([Int], [Int]) -> m ([Int], [Int])
lhs mp p x (ys, zs) =
  mbind (mmonad mp) (filt mp (const' True) (ys, zs)) (mreturn (mmonad mp))
  
{-@ reflect kleisli @-}
{-@ kleisli :: om : OurMonad m
            ->  f : (a -> m b)
            ->  g : (b -> m c)
            ->  x : a
            -> {v : m c | v = kleisli om f g x} @-}
kleisli :: OurMonad m -> (a -> m b) -> (b -> m c) -> a -> m c
kleisli om f g x = mbind om (f x) g

{-@ reflect rhs @-}
rhs :: MonadPlus m -> Int -> Int -> ([Int], [Int]) -> m ([Int], [Int])
rhs mp p x =
  kleisli (mmonad mp) (filt mp (const' True)) (mreturn (mmonad mp))
  
{-@ kp :: om : OurMonad m
            ->  f : (a -> m b)
            ->  g : (b -> m c)
            ->  x : a
            -> {v : () | kleisli om f g x = mbind om (f x) g} @-}
kp :: OurMonad m -> (a -> m b) -> (b -> m c) -> a -> ()
kp om f g x = ()
  
{-@ rewriteWith proof [kp] @-}
{-@ proof ::
           mp : MonadPlus m
        ->  p : Int
        ->  x : Int
        ->  tupl : ([Int], [Int])
        ->{ v : () |
         lhs mp p x tupl =
         rhs mp p x tupl
      }
@-}
proof :: MonadPlus m -> Int -> Int -> ([Int], [Int]) -> ()
proof mp p x (ys,zs) = ()
