{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--totality"         @-}
{-@ LIQUID "--exact-data-cons"  @-}
{-@ LIQUID "--alphaequivalence" @-}
{-@ LIQUID "--betaequivalence"  @-}
{-@ LIQUID "--normalform"       @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts      #-}

module MonadReader where

import Prelude hiding (return, Maybe(..), (>>=))

import Proves
import Helper 

-- | Monad Laws :
-- | Left identity:	  return a >>= f  ≡ f a
-- | Right identity:	m >>= return    ≡ m
-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

{-@ data Reader r a = Reader { runIdentity :: r -> a } @-}
data Reader r a     = Reader { runIdentity :: r -> a }

{-@ axiomatize return @-}
return :: a -> Reader r a
return x = Reader (\r -> x)

{-@ axiomatize bind @-}
bind :: Reader r a -> (a -> Reader r b) -> Reader r b
bind (Reader x) f = Reader (\r -> fromReader (f (x r)) r)

{-@ measure fromReader @-}
fromReader :: Reader r a -> r -> a 
fromReader (Reader f) = f

-- NV TODO the following is needed because Reader is not interpreted by
-- Contraints.Generate.lamExpr

{-@ axiomatize reader @-}
reader x = Reader x 

 
{-@ readerId :: f:(Reader r a) -> {f == Reader (fromReader f)} @-} 
readerId :: (Reader r a) -> Proof 
readerId (Reader f)  
  =   Reader (fromReader (Reader f))
  ==. Reader f 
  *** QED 


-- | Left Identity
{-@ left_identity :: x:a -> f:(a -> Reader r b) -> { bind (return x) f == f x } @-}
left_identity :: Arg r => a -> (a -> Reader r b) -> Proof
left_identity x f
  =   bind (return x) f 
  ==. bind (Reader (\r -> x)) f
  ==. Reader (\r' -> fromReader (f ((\r -> x) r')) r')
  ==. Reader (\r' -> fromReader (f x) r') ? left_identity_helper x f 
  ==. Reader (fromReader (f x)) ? lambda_expand (fromReader (f x))
  ==. f x                       ? readerId (f x)
  *** QED 


{-@ left_identity_helper :: x:a -> f:(a -> Reader r b) 
  -> {  (\r':r -> (fromReader (f ((\r:r -> x) (r')) ) (r'))) ==  (\r':r -> (fromReader (f x) (r')))  } @-}
left_identity_helper :: Arg r => a -> (a -> Reader r b) -> Proof
left_identity_helper x f
  =   simpleProof

-- | Right Identity


{-@ right_identity :: x:Reader r a -> { bind x return == x }
 @-}
right_identity :: Arg r => Reader r a -> Proof
right_identity (Reader x)
  =   bind (Reader x) return
  ==. Reader (\r -> fromReader (return (x r)) r)
  ==. Reader (\r -> fromReader (reader (\r' ->  (x r))) (r))
       ? right_identity_helper x 
  ==. Reader (\r -> (\r' ->  (x r)) (r)) 
       ? right_identity_helper1 x 
  ==. Reader (\r -> x r)           
       -- ? right_identity_helper2 x       
  ==. Reader x                           
       ? lambda_expand x 
  *** QED 


right_identity_helper1 :: Arg r => (r -> a) -> Proof 
{-@ right_identity_helper1 :: Arg r => x:(r -> a) 
  -> {(\r:r -> fromReader (reader (\r':r ->  (x r))) (r)) == (\r:r -> (\r':r ->  (x r)) (r))} @-}
right_identity_helper1 x =
  ((\r -> (\r' ->  (x r)) (r)) =*=. (\r -> fromReader (reader (\r' ->  (x r))) (r)))
    (right_identity_helper1_body x) *** QED 


right_identity_helper1_body :: Arg r => (r -> a) -> r -> Proof 
{-@ right_identity_helper1_body :: Arg r => x:(r -> a) -> r:r 
  -> {(fromReader (reader (\r':r ->  (x r))) (r) == (\r':r ->  (x r)) (r))
    && ((\r:r -> fromReader (reader (\r':r ->  (x r))) (r)) (r) == (fromReader (reader (\r':r ->  (x r))) (r))) 
    && ((\r:r -> (\r':r ->  (x r)) (r)) (r) == ((\r':r ->  (x r)) (r)))
    } @-}
right_identity_helper1_body x r
  =  fromReader (reader (\r' -> (x r))) r 
  ==. (\r' -> x r) r 
  *** QED 


right_identity_helper2 :: Arg r => (r -> a) -> Proof 
{-@ right_identity_helper2 :: Arg r => x:(r -> a) 
  -> { (\r:r -> (\r':r ->  (x r)) (r)) ==  (\r:r -> x r) } @-}
right_identity_helper2 _ = simpleProof


right_identity_helper :: Arg r => (r -> a) -> Proof 
{-@ right_identity_helper :: Arg r => x:(r -> a) 
  -> {(\r:r -> fromReader (return (x r)) r) == (\r:r -> fromReader (reader (\r':r ->  (x r))) (r))} @-}
right_identity_helper x
  =  (
     (\r -> fromReader (return (x r)) r)
     =*=. 
     (\r -> fromReader (reader (\r' ->  (x r))) (r))
     )  (right_identity_helper_body x) *** QED 

right_identity_helper_body :: Arg r => (r -> a) -> r -> Proof 
{-@ right_identity_helper_body :: Arg r => x:(r -> a) -> r:r
  -> { (fromReader (return (x r)) r == fromReader (reader (\r':r ->  (x r))) (r))
       && (((\r:r -> fromReader (return (x r)) r)) (r) == (fromReader (return (x r)) r))
       && ((\r:r -> fromReader (reader (\r':r ->  (x r))) (r))(r) == (fromReader (reader (\r':r ->  (x r))) (r)))
      } @-}
right_identity_helper_body x r 
  =   fromReader (return (x r)) r
  ==. fromReader (reader (\r' ->  (x r))) r
  *** QED 

-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)
{-@ associativity :: x:Reader r a -> f: (a -> Reader r a) -> g:(a -> Reader r a) 
  -> {bind (bind x f) g      ==  bind x (\r4:a ->(bind (f r4) g)) } @-}
associativity :: (Arg r, Arg a) =>  Reader r a -> (a -> Reader r a) -> (a -> Reader r a) -> Proof
associativity (Reader x) f g
  =   bind (bind (Reader x) f) g
  -- unfold inner bind 
  ==. bind (Reader (\r1 -> fromReader (f (x r1)) r1)) g 
  -- unfold outer bind 
  ==. Reader (\r2 -> fromReader (g ((\r1 -> fromReader (f (x r1)) r1) (r2))) (r2))
  -- apply    r1 := r2
  ==. Reader (\r2 -> fromReader (g (fromReader (f (x r2)) r2) )  r2)
  -- abstract r3 := r2 
  ==. Reader (\r2 -> 
          (\r3 -> fromReader (g ((fromReader (f (x r2))) r3) ) r3)
         r2)
  -- apply measure fromReader (Reader f) == f 
  ==. Reader (\r2 -> fromReader (
          (reader (\r3 -> fromReader (g ((fromReader (f (x r2))) r3) ) r3))
        ) r2)
        ? associativity_helper0 x f g 
  -- abstract r4 := x r2 
  ==. Reader (\r2 -> fromReader ((\r4 -> 
          (reader (\r3 -> fromReader (g ((fromReader (f r4)) r3) ) r3))
        ) (x r2)) r2) 
      ? associativity_helper2 x f g 
  -- fold (bind (f r4) g)
  ==. Reader (\r2 -> fromReader ((\r4 -> 
           (bind (f r4) g)
        ) (x r2)) r2)  
     ? associativity_helper1 x f g 
  -- fold bind 
  ==. bind (Reader x) (\r4 ->(bind (f r4) g))
  *** QED  

{-@ associativity_helper0 :: x:(r -> a) -> f:(a -> Reader r b) -> g:(b -> Reader r c) 
  -> {  (\r2:r -> (\r3:r -> fromReader (g (fromReader (f ( x r2)) r3)) (r3)) (r2)) 
      ==   (\r2:r -> (fromReader (reader (\r3:r -> fromReader (g (fromReader (f (x r2)) r3)) (r3)))) (r2)) 
          } @-}
associativity_helper0 :: Arg r => (r -> a) -> (a -> Reader r b) -> (b -> Reader r c) -> Proof
associativity_helper0 x f g
  =    ((\r2 -> (\r3 -> fromReader (g (fromReader (f ( x r2)) r3)) (r3)) (r2)) 
  =*=.  (\r2 -> fromReader (reader (\r3 -> fromReader (g (fromReader (f (x r2)) r3)) (r3))) (r2)))
         (associativity_helper0_body x f g) *** QED 
          
associativity_helper0_body :: (r -> a) -> (a -> Reader r b) -> (b -> Reader r c)-> r  -> Proof
{-@ associativity_helper0_body :: x:(r -> a) -> f:(a -> Reader r b) -> g:(b -> Reader r c) -> r2:r
  -> {    (\r3:r -> fromReader (g (fromReader (f ( x r2)) r3)) (r3)) (r2)
      ==  (fromReader (reader (\r3:r -> fromReader (g (fromReader (f (x r2)) r3)) (r3)))) (r2)
       && 
           ((\r2:r -> (\r3:r -> fromReader (g (fromReader (f ( x r2)) r3)) (r3)) (r2))) (r2) == (\r3:r -> fromReader (g (fromReader (f ( x r2)) r3)) (r3)) (r2)
       && 
           (\r2:r -> (fromReader (reader (\r3:r -> fromReader (g (fromReader (f (x r2)) r3)) (r3)))) (r2)) (r2) == (fromReader (reader (\r3:r -> fromReader (g (fromReader (f (x r2)) r3)) (r3)))) (r2)
          } @-}
associativity_helper0_body x f g r2
  = readerId' (\r3 -> fromReader (g (fromReader (f ( x r2)) r3)) (r3))

{-@ readerId' :: x:(r -> a) -> {x == fromReader (reader x)} @-} 
readerId' :: (r -> a) -> Proof 
readerId' x  
  =   fromReader (reader x)
  ==. fromReader (Reader x)
  ==. x 
  *** QED 


{-@ associativity_helper2 :: x:(r -> a) -> f:(a -> Reader r b) -> g:(b -> Reader r c) 
  -> {  (\r2:r -> fromReader (reader (\r3:r -> fromReader (g (fromReader (f (x r2)) r3)) (r3))) (r2))  
      ==   (\r2:r -> fromReader ( (\r4:a -> ( reader (\r3:r -> fromReader (g (fromReader (f r4 ) r3)) (r3))))  (x r2)) (r2))  
         } @-}
associativity_helper2 :: (r -> a) -> (a -> Reader r b) -> (b -> Reader r c) -> Proof
associativity_helper2 x f g = simpleProof

{-@ associativity_helper1 :: x:(r -> a) -> f:(a -> Reader r b) -> g:(b -> Reader r c) 
  -> {   (\r2:r -> fromReader ( (\r4:a -> ( reader (\r3:r -> fromReader (g (fromReader (f r4 ) r3)) (r3))))  (x r2)) (r2))  
      ==    (\r2:r -> fromReader ( (\r4:a -> ( bind (f r4) g))  (x r2)) (r2))  
    } @-}
associativity_helper1 :: (Arg r, Arg a) => (r -> a) -> (a -> Reader r b) -> (b -> Reader r c) -> Proof
associativity_helper1 x f g
  = ((\r2 -> fromReader ( (\r4 -> ( reader (\r3 -> fromReader (g (fromReader (f r4 ) r3)) (r3))))  (x r2)) (r2))  
      =*=.    (\r2 -> fromReader ( (\r4 -> ( bind (f r4) g))  (x r2)) (r2))  
    ) (associativity_helper1_body x f g)  *** QED 

{-@ associativity_helper1_body :: x:(r -> a) -> f:(a -> Reader r b) -> g:(b -> Reader r c) -> r2:r
  -> {  fromReader ( (\r4:a -> ( reader (\r3:r -> fromReader (g (fromReader (f r4 ) r3)) (r3))))  (x r2)) (r2)  
      ==   fromReader ( (\r4:a -> ( bind (f r4) g))  (x r2)) (r2)
      && 
        ((\r2:r -> fromReader ( (\r4:a -> ( reader (\r3:r -> fromReader (g (fromReader (f r4 ) r3)) (r3))))  (x r2)) (r2))) (r2)
        == fromReader ( (\r4:a -> ( reader (\r3:r -> fromReader (g (fromReader (f r4 ) r3)) (r3))))  (x r2)) (r2)
      && 
        (\r2:r -> fromReader ( (\r4:a -> ( bind (f r4) g))  (x r2)) (r2)) (r2)
        == fromReader ( (\r4:a -> ( bind (f r4) g))  (x r2)) (r2)
    } @-}
associativity_helper1_body :: (Arg r, Arg a ) => (r -> a) -> (a -> Reader r b) -> (b -> Reader r c) -> r -> Proof
associativity_helper1_body x f g r2 
  =   fromReader ( (\r4 -> ( reader (\r3 -> fromReader (g (fromReader (f r4 ) r3)) (r3))))  (x r2)) (r2)
  ==. fromReader ( (\r4 -> ( bind (f r4) g))  (x r2)) (r2)
      ? helper_of_helper x f g r2
  *** QED 


{-@ helper_of_helper :: x:(r -> a) -> f:(a -> Reader r b) -> g:(b -> Reader r c) -> r2:r
  -> {   \r4:a -> (reader (\r3:r -> fromReader (g (fromReader (f r4 ) r3)) (r3)))
      == \r4:a -> (bind (f r4) g)
    } @-}
helper_of_helper :: (Arg r, Arg a) => (r -> a) -> (a -> Reader r b) -> (b -> Reader r c) -> r -> Proof
helper_of_helper x f g r2 
  =  ( (\r4 -> (reader (\r3 -> fromReader (g (fromReader (f r4 ) r3)) (r3))))
      =*=. (\r4 -> (bind (f r4) g))) (helper_of_helper_body x f g r2) *** QED 

{-@ helper_of_helper_body :: x:(r -> a) -> f:(a -> Reader r b) -> g:(b -> Reader r c) -> r2:r -> r4:a
  -> {   (reader (\r3:r -> fromReader (g (fromReader (f r4 ) r3)) (r3)))
      == (bind (f r4) g)
      && 
         (\r4:a -> (reader (\r3:r -> fromReader (g (fromReader (f r4 ) r3)) (r3)))) (r4)
      ==  (reader (\r3:r -> fromReader (g (fromReader (f r4 ) r3)) (r3)))
      && 
         (\r4:a -> (bind (f r4) g)) (r4) == (bind (f r4) g)

    } @-}
helper_of_helper_body :: Arg r => (r -> a) -> (a -> Reader r b) -> (b -> Reader r c) -> r -> a -> Proof
helper_of_helper_body x f g r2 r4 
  = case f r4 of 
      Reader _ -> reader (\r3 -> fromReader (g (fromReader (f r4 ) r3)) (r3)) 
                  ==. bind (f r4) g 
                   *** QED 



{-@ helper_of_helper_body' :: x:(r -> a) -> y:(Reader r b) -> g:(b -> Reader r c) -> r2:r -> r4:a
  -> {   (Reader (\r3:r -> fromReader (g ( (fromReader y) (r3))) (r3)))
      == (bind y g)
    } @-}
helper_of_helper_body' :: Arg r => (r -> a) -> (Reader r b) -> (b -> Reader r c) -> r -> a -> Proof
helper_of_helper_body' x y@(Reader _) g r2 r4  
  =   reader (\r3 -> fromReader (g ( (fromReader y) r3)) (r3)) 
  ==. bind y g 
  *** QED 



{-@ qual :: f:(r -> a) -> {v:Reader r a | v == Reader f} @-}
qual :: (r -> a) -> Reader r a 
qual = Reader 