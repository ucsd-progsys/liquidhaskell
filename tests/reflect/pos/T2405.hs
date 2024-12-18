{-# OPTIONS_GHC -O #-}

{-@ LIQUID "--reflection" @-}

-- | Compiling with optimizations causes some rewrite rules to fire in the simple
-- optimizer during desugaring. In the case of list functions, stream fusion rewrite
-- rules are enabled, causing @singleton x = [x]@ to be desugared as
--
-- > singleton = \ @a x -> build (\ @a c_dE7 n_dE8 -> c_dE7 x n_dE8)
--
-- which then cannot be reflected because of the lambda expression.
--
-- LH disables rewrite rules when desugaring for verification, and this test is an
-- attempt to show the need for it.
--
module T2405 where

{-@ reflect singleton @-}
singleton :: a -> [a]
singleton x = [x]
