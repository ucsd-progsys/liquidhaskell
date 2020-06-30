{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module SemiGroup where

    import Prelude hiding (mappend)
    import Language.Haskell.Liquid.Equational
    
    class SG a where 
      mappend :: a -> a -> a 
    
    {-@ 
    class laws SG a where 
      assocSG :: x:a -> y:a -> z:a 
              -> { mappend x (mappend y z) == mappend (mappend x y) z }
     @-}
    
    
    assocSG :: SG a => a -> a -> a -> () 
    assocSG x y z = () 
    
    
    instance SG [a] where 
      mappend = mappendList

    {-@ reflect mappendList @-}
    mappendList :: [a] -> [a] -> [a]
    mappendList []     ys = ys 
    mappendList (x:xs) ys = x:mappendList xs ys 
    
    {-@ 
    instance laws SG a => SG [a] where 
      mappend = mappendList
      assocSG = mappendListAssoc
    @-}

    {-@ mappendListAssoc :: x:[a] -> y:[a] -> z:[a] 
          -> { mappendList x (mappendList y z) == mappendList (mappendList x y) z } @-}
    mappendListAssoc :: [a] -> [a] -> [a] -> () 
    mappendListAssoc xs ys zs
      = ()  
    
