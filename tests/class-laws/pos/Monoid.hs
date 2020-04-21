{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Monoid where

    import Prelude hiding (mappend, mempty, Monoid)
    import Language.Haskell.Liquid.Equational
    import SemiGroup
    
    class SG a => Monoid a where 
      mempty :: a 
    
    {-@ 
    class laws SG a => Monoid a where 
      leftId  :: x:a -> { mappend mempty x == x }
      rightId :: x:a -> { mappend x mempty == x }
     @-}
    
    rightId, leftId :: Monoid a => a -> () 
    leftId  x = () 
    rightId x = () 
    
    instance Monoid Int where 
      mempty = memptyInt 

    {-@ reflect memptyInt @-}
    memptyInt :: Int 
    memptyInt = 0 

    leftIdInt  :: Int -> () 
    rightIdInt :: Int -> () 
    {-@ leftIdInt  :: x:Int -> { mappendInt memptyInt x == x } @-}
    {-@ rightIdInt :: x:Int -> { mappendInt x memptyInt == x } @-}
    leftIdInt _  = () 
    rightIdInt _ = () 

    {-@ 
    instance laws Monoid Int where 
      mempty  = memptyInt 
      mappend = mappendInt 
      leftId  = leftIdInt
      rightId = rightIdInt
    @-}


    instance SG a => Monoid (Maybe a) where 
      mempty = Nothing 
      
    instance Monoid [a] where 
      mempty = [] 
      

    -- GRRRRRR ERROR   
    {-@ reflect foo @-}  
    foo x = Just x
    foo :: a -> Maybe a 
