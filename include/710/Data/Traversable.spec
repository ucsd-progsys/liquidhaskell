module spec Data.Traversable where

Data.Traversable.sequence :: Data.Traversable.Traversable t => GHC.Base.Monad m => xs:t (m a) -> m (t {v:[a] | (len v) = (len xs)})
