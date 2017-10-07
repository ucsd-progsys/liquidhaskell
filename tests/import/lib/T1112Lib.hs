module T1112Lib where

data Product f g p = Product (f p) (g p) deriving Eq
