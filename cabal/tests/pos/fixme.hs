{-# LANGUAGE ScopedTypeVariables #-}

module Test00c where

import Language.Haskell.Liquid.Prelude

prop_abs = (\(z:: Int) -> assert True) $ (0 :: Int)
