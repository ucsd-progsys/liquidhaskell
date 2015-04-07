module spec Control.Monad where

sequence :: GHC.Base.Monad m => xs:[m a] -> m {v:[a] | (len v) = (len xs)}
