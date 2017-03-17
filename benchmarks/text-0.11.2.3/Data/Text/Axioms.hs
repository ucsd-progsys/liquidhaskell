module Data.Text.Axioms where

import qualified Data.Text.Array as A
import Data.Text.Internal


{-@ axiom_numchars_append
      :: a:Text -> b:Text -> t:Text
      -> {v:Bool | (v <=> (((tlen t) = (tlen a) + (tlen b))
                                  => ((tlength t) = (tlength a) + (tlength b))))}
 @-}
axiom_numchars_append :: Text -> Text -> Text -> Bool
axiom_numchars_append = undefined

{-@ axiom_numchars_replicate
      :: t1:Text -> t2:Text
      -> {v:Bool | (v <=> (((tlen t2) >= (tlen t1))
                                  => ((tlength t2) >= (tlength t1))))}
  @-}
axiom_numchars_replicate :: Text -> Text -> Bool
axiom_numchars_replicate = undefined

{-@ axiom_numchars_concat
      :: t:Text -> ts:[Text] -> l:Int
      -> {v:Bool | (v <=> ((l = (sum_tlens ts))
                                  => ((tlength t) = (sum_tlengths ts))))}
  @-}
axiom_numchars_concat :: Text -> [Text] -> Int -> Bool
axiom_numchars_concat = undefined


{-@ axiom_numchars_split
      :: t:Text
      -> i:Int
      -> {v:Bool | (v <=>
                    ((numchars (tarr t) (toff t) (tlen t))
                     = ((numchars (tarr t) (toff t) i)
                        + (numchars (tarr t) ((toff t) + i) ((tlen t) - i)))))}
  @-}
axiom_numchars_split :: Text -> Int -> Bool
axiom_numchars_split = undefined

