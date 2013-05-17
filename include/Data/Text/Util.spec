module spec Data.Text.Util where

intersperse :: a -> as:[a] -> {v:[a] | (len v) >= (len as)}
