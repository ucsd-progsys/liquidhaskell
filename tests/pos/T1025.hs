{-@ LIQUID "--exactdc"     @-}                                                            
{-@ LIQUID "--higherorder" @-}                                                            
{-@ LIQUID "--totality"    @-}                                                            
module Bug where                                                                          
                                                                                          
import Language.Haskell.Liquid.ProofCombinators                                           
                                                                                          
{-@ assume Left  :: a:a -> { v:Either a b | v == Left  a && select_Left_1  v == a && is_Left v && not (is_Right v) } @-}
{-@ assume Right :: b:b -> { v:Either a b | v == Right b && select_Right_1 v == b && not (is_Left v) && is_Right v } @-}
                                                                                          
{-@ measure select_Left_1  :: Either a b -> a @-}                                         
{-@ measure select_Right_1 :: Either a b -> b @-}                                         
                                                                                          
{-@ measure is_Left  :: Either a b -> Bool @-}                                            
{-@ measure is_Right :: Either a b -> Bool @-}                                            
                                                                                          
{-@ axiomatize eqEither @-}                                                               
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
