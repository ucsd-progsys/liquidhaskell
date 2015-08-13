module spec Data.Traversable where

Data.Traversable.sequence :: Data.Traversable.Traversable t => forall m a. GHC.Base.Monad m => xs:t (m a) -> m ({v:t a | len v = len xs})
