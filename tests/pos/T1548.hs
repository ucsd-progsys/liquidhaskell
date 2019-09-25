{-@ LIQUID "--reflection" @-}


module T1548 where

import Language.Haskell.Liquid.Equational 


h :: (b -> d) -> (a,b) -> Proof
{-@ h :: g:(b -> d) -> p:(a,b) -> { (snd . second g) (p) == (g . snd) (p) } @-}
h g p =   (snd . second g) p
      ==. snd (second g p)
          ? sndSecond g p
      ==. g (snd p)
      ==. (g . snd) p
      *** QED


{-@ reflect second @-}
second :: (b -> d) -> ((a,b) -> (a,d))
second g (a,b) = (a, g b)

{-@ sndSecond :: g:(b -> d) -> p:(a,b) -> { snd (second g p) == g (snd p) } @-}
sndSecond :: (b -> d) -> (a,b) -> Proof
sndSecond g (a,b)
  =   snd (second g (a,b))
  ==. snd (a,g b)
  ==. g b
  ==. g (snd (a,b))
  *** QED