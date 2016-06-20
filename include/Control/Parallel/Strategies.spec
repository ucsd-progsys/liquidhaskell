module spec Control.Parallel.Strategies where

assume withStrategy :: Strategy a -> x:a -> {v:a | v == x}
