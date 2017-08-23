{-@ LIQUID "--exactdc"     @-}
{-@ LIQUID "--higherorder" @-}

module Bug where

import Language.Haskell.Liquid.ProofCombinators

{-@ data Either a b = Left a | Right b @-}

-- RJ: With `adt` we don't need the below, they are generated from the above.

{- assume Left  :: a:a -> { v:Either a b | v == Left  a && lqdc##select##Left##1  v == a && lqdc##is##Left v && not (lqdc##is##Right v) } @-}

{- assume Right :: b:b -> { v:Either a b | v == Right b && lqdc##select##Right##1 v == b && not (lqdc##is##Left v) && lqdc##is##Right v } @-}

{- measure lqdc##select##Left##1  :: Either a b -> a

    lqdc##select##Left##1 (Left x) = x
  -}

{- measure lqdc##select##Right##1 :: Either a b -> b
    lqdc##select##Right##1 (Right x) = x
  -}

{- measure lqdc##is##Left  :: Either a b -> Bool
    lqdc##is##Left (Right x) = false
    lqdc##is##Left (Left x)  = true
  -}

{- measure lqdc##is##Right :: Either a b -> Bool
    lqdc##is##Right (Right x) = true
    lqdc##is##Right (Left x)  = false
  -}

{-@ reflect eqEither @-}
eqEither :: (a -> a -> Bool) -> (b -> b -> Bool)
         -> Either a b -> Either a b -> Bool
eqEither eqA _   (Left  x) (Left  y) = eqA x y
eqEither _   eqB (Right x) (Right y) = eqB x y
eqEither _   _   (Left  _) (Right _) = False
eqEither _   _   (Right _) (Left  _) = False

{-@ eqEitherRefl :: eqA:(a -> a -> Bool) -> eqARefl:(x:a -> { eqA x x })
                 -> eqB:(b -> b -> Bool) -> eqBRefl:(y:b -> { eqB y y })
                 -> p:Either a b
                 -> { eqEither eqA eqB p p }
@-}
eqEitherRefl :: (a -> a -> Bool) -> (a -> Proof)
             -> (b -> b -> Bool) -> (b -> Proof)
             -> Either a b -> Proof
eqEitherRefl eqA eqARefl eqB _ p@(Left x) =
      eqEither eqA eqB p p
  ==. eqA x x
  ==. True ? eqARefl x
  *** QED
eqEitherRefl eqA _ eqB eqBRefl p@(Right y) =
      eqEither eqA eqB p p
  ==. eqB y y
  ==. True ? eqBRefl y
  *** QED
