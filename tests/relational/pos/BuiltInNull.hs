module Fixme where

{-@ reflect null' @-}
null' :: [Int] -> Bool
null' [] = True
null' _  = False

{-@ relational null' ~ null' :: { l1:_ -> _
                              ~ l2:_ -> _
                             | len l1 = len l2 :=> Fixme.null' l1 = Fixme.null' l2 }@-}
