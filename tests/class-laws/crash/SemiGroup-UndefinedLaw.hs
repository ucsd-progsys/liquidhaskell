{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module SemiGroup where

    import Prelude hiding (mappend)
    import Language.Haskell.Liquid.Equational
    
    class SG a where 
      mappend :: a -> a -> a 
    
    {-@ 
    class laws SG a where 
      assocSG  :: x:a -> y:a -> z:a 
              -> { mappend x (mappend y z) == mappend (mappend x y) z }
     @-}
    
    
    assocSG :: SG a => a -> a -> a -> () 
    assocSG x y z = () 
    
    instance SG Int where 
      mappend = mappendInt 

    {-@ 
    instance laws SG Int where 
      mappend = mappendInt
      assocSGMisTypes = mappendIntAssoc
    @-}
    
    
    {-@ reflect mappendInt @-}  
    mappendInt :: Int -> Int -> Int 
    mappendInt x y = x + y 
    
    {-@ mappendIntAssoc :: x:Int -> y:Int -> z:Int 
      -> { mappendInt x (mappendInt y z) == mappendInt (mappendInt x y) z } @-}
    mappendIntAssoc :: Int -> Int -> Int -> () 
    mappendIntAssoc _ _ _ = () 
    