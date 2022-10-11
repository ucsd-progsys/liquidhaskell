module T1571 where

  data TaggedT m a = TaggedT (m a)
  
  class MonadController m where
    respond :: a -> m ()
  
  {-@
  instance MonadController m => MonadController (TaggedT m) where
    respond :: a -> TaggedT m ()
  @-}
  instance MonadController m => MonadController (TaggedT m) where
    respond = undefined
