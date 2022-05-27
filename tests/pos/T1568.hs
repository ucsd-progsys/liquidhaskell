module T1568 where

    {-@ data IdentityT m a = IdentityT (m a) @-}
    data IdentityT m a = IdentityT (m a)
    
    class MyMonad m where
      myReturn :: a -> m a
    
    {-@
    instance MyMonad (IdentityT m) where
      myReturn :: a -> IdentityT m a
    @-}
    instance MyMonad (IdentityT m) where
      myReturn = undefined
    
    -- When using the real Monad class the error doesn't happen until return is
    -- actually used for some reason
    {-@ testMyReturn :: a -> IdentityT m a @-}
    testMyReturn :: a -> IdentityT m a
    testMyReturn x = myReturn x
