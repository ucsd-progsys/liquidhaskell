module spec Control.Parallel.Strategies where

assume withStrategy :: Control.Parallel.Strategies.Strategy a -> x:a -> {v:a | v == x}
