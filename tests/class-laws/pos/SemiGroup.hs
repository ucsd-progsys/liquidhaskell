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
    
    instance SG Int where 
      mappend = mappendInt 

    {-@ 
    instance laws SG Int where 
      mappend = mappendInt
      assocSG = mappendIntAssoc
    @-}
    
    
    {-@ reflect mappendInt @-}  
    mappendInt :: Int -> Int -> Int 
    mappendInt x y = x + y 
    
    {-@ mappendIntAssoc :: x:Int -> y:Int -> z:Int 
          -> { mappendInt x (mappendInt y z) == mappendInt (mappendInt x y) z } @-}
    mappendIntAssoc :: Int -> Int -> Int -> () 
    mappendIntAssoc _ _ _ = () 
    
    instance SG a => SG (Maybe a) where 
      mappend = mappendMaybe 
    
    {-@ reflect mappendMaybe @-}
    mappendMaybe :: SG a => Maybe a -> Maybe a -> Maybe a 
    mappendMaybe (Just x) (Just y) = Just (x `mappend` y)
    mappendMaybe _ _               = Nothing 
    
    {-@ 
    instance laws SG a => SG (Maybe a) where 
      mappend = mappendMaybe
      assocSG = mappendMaybeAssoc
    @-}
    
    {-@ mappendMaybeAssoc :: SG a => x:Maybe a -> y:Maybe a -> z:Maybe a 
          -> { mappendMaybe x (mappendMaybe y z) == mappendMaybe (mappendMaybe x y) z } @-}
    mappendMaybeAssoc :: SG a => Maybe a -> Maybe a -> Maybe a -> () 
    mappendMaybeAssoc (Just x) (Just y) (Just z)
      = assocSG x y z 
    mappendMaybeAssoc _ _ _ = () 
    
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
    mappendListAssoc (x:xs) ys zs
      = mappendListAssoc xs ys zs  
    mappendListAssoc _ _ _ = () 
    
