
-- Test for https://github.com/ucsd-progsys/liquidhaskell/issues/1907

module T1907 where

{-@ foldr' :: forall <inv :: [a] -> b -> Bool>.
              (a -> b -> b) -> b<inv []> -> xs:[a] -> b<inv xs>
  @-}
foldr' op b = go
  where
    {-@ go :: forall <inv :: [a] -> b -> Bool>.
              xs:[a] -> b<inv xs>
      @-} 
    go []    = b
    go (h:t) = op h (go t)


{-@ mlength :: zs:[a] -> {v:_ | v == 42 * (len zs) } @-}
mlength = foldr' (\_ n -> n + 1) 0
