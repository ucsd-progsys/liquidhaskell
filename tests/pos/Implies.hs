module Implies where

{-@ inline implies @-}
implies p q = (not p) || q

