{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}


{-@ LIQUID "--cores=10"            @-}
{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}

module Main where

import Prelude hiding ( mempty, mappend, id, mconcat, map
                      , take, drop  
                      , error, undefined
                      )


import System.Environment   
import Data.String hiding (fromString)
import GHC.TypeLits
import Data.Maybe 

import String
import Language.Haskell.Liquid.ProofCombinators 

import Data.Proxy 

{-@ symbolVal :: forall n proxy. KnownSymbol n => x:proxy n 
  -> {v:String | v == n && v == symbolVal x } @-}
{-@ measure symbolVal :: p n -> String @-}

-------------------------------------------------------------------------------
------------ | String Matching Main Theorem  ----------------------------------
-------------------------------------------------------------------------------

{-@ distributionOfStringMatching :: MI target -> is:SMTString  -> n:Int -> m:Int
   -> {toMI is == pmconcat m (map toMI (chunkString n is))} @-}

distributionOfStringMatching :: forall (target :: Symbol). (KnownSymbol target) => MI target -> SMTString -> Int -> Int -> Proof
distributionOfStringMatching _ is n m  
  =   (pmconcat m (map toMI (chunkString n is)) :: MI target)
  ==. mconcat (map toMI (chunkString n is))
       ? pmconcatEquivalence m (map toMI (chunkString n is) :: List (MI target))
  ==. toMI is 
       ? distributionOfMI (mempty :: MI target) is n 
  *** QED 


-------------------------------------------------------------------------------
------------ | Interface ------------------------------------------------------
-------------------------------------------------------------------------------

main :: IO ()
main = 
  do args      <- getArgs
     case args of 
       (i:fname:target:_) -> do input <- fromString <$> readFile fname 
                                runMatching (read i :: Int) input target
       _                -> putStrLn $ "Wrong input: You need to provide the chunksize," ++
                                      "the input filename and the target string. For example:\n\n\n" ++ 
                                      "./StringIndexing 10 input.txt abcab\n\n"
     

runMatching :: Int -> SMTString -> String -> IO ()
runMatching chunksize input tg =
  case someSymbolVal tg of 
    SomeSymbol (_ :: Proxy target) -> do            
      let mi1    = toMI input :: MI target 
      let is1    = indicesMI mi1 
      putStrLn   $ "Serial   Indices: " ++ show is1
      let mi2    = toMIPar chunksize input :: MI target 
      let is2    = indicesMI mi2 
      putStrLn   $ "Parallel Indices: " ++ show is2
      putStrLn   $ "Are equal? " ++ show (is1 == is2)

test = indicesMI (toMI (fromString $ clone 100 "ababcabcab")  :: MI "abcab" )
  where
    clone i xs = concat (replicate i xs) 



{-@ reflect toMI @-}
toMI :: forall (target :: Symbol). (KnownSymbol target) => SMTString -> MI target 
toMI input  
  | stringLen input == 0 
  = mempty
  | otherwise          
  = MI input (makeIndices input (fromString (symbolVal (Proxy :: Proxy target))) 0 (stringLen input - 1))

toMIPar :: forall (target :: Symbol). (KnownSymbol target) => Int -> SMTString -> MI target  
toMIPar chunksize input 
  = pmconcat chunksize (map toMI (chunkString chunksize input))

-------------------------------------------------------------------------------
----------  Indexing Structure Definition -------------------------------------
-------------------------------------------------------------------------------

data MI (target :: Symbol) where 
  MI :: SMTString       -- | input string
     -> (List Int)      -- | valid indices of target in input
     -> MI target
  deriving (Show)

{-@ data MI target 
  = MI { input   :: SMTString
       , indices :: List (GoodIndex input target)
       } @-}

{-@ type GoodIndex Input Target 
  = {i:Int | IsGoodIndex Input Target i }
  @-}

{-@ type GoodIndexTwo Input X Target 
  = {i:Int | (IsGoodIndex Input Target i)  && (IsGoodIndex (concatString Input X) Target i) }
  @-}


{-@ predicate IsGoodIndex Input Target I
  =  (subString Input I (stringLen Target)  == Target)
  && (I + stringLen Target <= stringLen Input)
  && (0 <= I)
  @-}

{-@ measure indicesMI @-}
indicesMI (MI _ is) = is 

{-@ measure inputMI @-}
inputMI (MI i _) = i 

-------------------------------------------------------------------------------
----------  Monoid Operators on MI --------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect mempty @-}
mempty :: forall (target :: Symbol). (KnownSymbol target) =>  MI target
mempty = MI stringEmp N

{-@ reflect mconcat @-}
mconcat :: forall (target :: Symbol). (KnownSymbol target) => List (MI target) -> MI target 
mconcat N        = mempty
mconcat (C x xs) = mappend x (mconcat xs)

{-@ reflect pmconcat @-}
pmconcat :: forall (target :: Symbol). (KnownSymbol target) => Int -> List (MI target) -> MI target 
{-@ pmconcat :: forall (target :: Symbol). (KnownSymbol target) => 
  Int -> is:List (MI target) -> MI target /[llen is] @-}

pmconcat i xs
  | i <= 1 
  = mconcat xs 
pmconcat i N   
  = mempty
pmconcat i (C x N) 
  = x
pmconcat i xs 
  = pmconcat i (map mconcat (chunk i xs))



{-@ reflect mappend @-}
mappend :: forall (target :: Symbol).  (KnownSymbol target) => MI target -> MI target -> MI target
mappend (MI i1 is1) (MI i2 is2)
  = MI (concatString i1 i2)
       ((castGoodIndexRightList (fromString (symbolVal (Proxy :: Proxy target))) i1 i2 is1
          `append`
        makeNewIndices i1 i2 (fromString (symbolVal (Proxy :: Proxy target)))
       ) `append`
       (map (shiftStringRight (fromString (symbolVal (Proxy :: Proxy target))) i1 i2) is2)) 

-- | Helpers 
{-@ reflect shiftStringRight @-}
shiftStringRight :: SMTString -> SMTString -> SMTString -> Int -> Int 
{-@ shiftStringRight :: target:SMTString -> left:SMTString -> right:SMTString -> i:GoodIndex right target 
  -> {v:(GoodIndex {concatString left right} target) | v == i + stringLen left } @-}
shiftStringRight target left right i 
  = cast (subStringConcatFront right left (stringLen target) i) (shift (stringLen left) i)

{-@ reflect makeNewIndices @-}
{-@ makeNewIndices :: s1:SMTString -> s2:SMTString -> target:SMTString -> List (GoodIndex {concatString s1 s2} target) @-}
makeNewIndices :: SMTString -> SMTString -> SMTString -> List Int 
makeNewIndices s1 s2 target
  | stringLen target < 2 
  = N
  | otherwise
  = makeIndices (concatString s1 s2) target
                (maxInt (stringLen s1 - (stringLen target-1)) 0)
                (stringLen s1 - 1)

{-@ reflect maxInt @-}
maxInt :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 

{-@ reflect shift @-}
shift :: Int -> Int -> Int 
shift x y = x + y 

-- | Casting good indices: the below operators are liquid casts and behave like id at runtime

-- NV: The recursion is required as there is no other way to (access &) cast _each_ element of the input list
{-@ reflect castGoodIndexRightList @-}
castGoodIndexRightList :: SMTString -> SMTString -> SMTString -> List Int -> List Int    
{-@ castGoodIndexRightList :: target:SMTString -> input:SMTString -> x:SMTString -> is:List (GoodIndex input target) 
    -> {v:List (GoodIndexTwo input x target) | v == is} @-}
castGoodIndexRightList target input x N 
  = N 
castGoodIndexRightList target input x (C i is) 
  = C (castGoodIndexRight target input x i) (castGoodIndexRightList target input x is)  


{-@ reflect castGoodIndexRight @-}
castGoodIndexRight :: SMTString -> SMTString -> SMTString -> Int -> Int  
{-@ castGoodIndexRight :: target:SMTString -> input:SMTString -> x:SMTString -> i:GoodIndex input target 
   -> {v:(GoodIndexTwo input x target)| v == i} @-}
castGoodIndexRight target input x i  = cast (subStringConcatBack input x (stringLen target) i) i


-------------------------------------------------------------------------------
----------  Indices' Generation -----------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect makeIndices @-}
makeIndices :: SMTString -> SMTString -> Int -> Int -> List Int 
{-@ makeIndices :: input:SMTString -> target:SMTString -> lo:Nat -> hi:Int -> List (GoodIndex input target) 
  / [hi - lo] @-}
makeIndices input target lo hi 
  | hi < lo 
  = N
  | lo == hi, isGoodIndex input target lo
  = lo `C` N
  | lo == hi 
  = N
makeIndices input target lo hi 
  | isGoodIndex input target lo
  = lo `C` (makeIndices input target (lo + 1) hi)
  | otherwise 
  =    makeIndices input target (lo + 1) hi 

{-@ reflect isGoodIndex @-}
isGoodIndex :: SMTString -> SMTString -> Int -> Bool 
{-@ isGoodIndex :: input:SMTString -> target:SMTString -> i:Int 
  -> {b:Bool | Prop b <=> IsGoodIndex input target i} @-}
isGoodIndex input target i 
  =  subString input i (stringLen target)  == target  
  && i + stringLen target <= stringLen input
  && 0 <= i    


-------------------------------------------------------------------------------
----------  List Structure ----------------------------------------------------
-------------------------------------------------------------------------------
   
data List a = N | C a (List a) deriving (Show, Eq)
{-@ data List [llen] a 
  = N | C {lhead :: a , ltail :: List a} @-}


{-@ measure llen @-}
{-@ llen :: List a -> Nat @-} 
llen :: List a -> Int 
llen N        = 0 
llen (C _ xs) = 1 + llen xs 

{-@ reflect map @-}
{-@ map :: (a -> b) -> is:List a -> {os:List b | llen is == llen os} @-}
map :: (a -> b) -> List a -> List b
map _ N        = N
map f (C x xs) = C (f x) (map f xs)

{-@ reflect append @-}
append :: List a -> List a -> List a 
append N        ys = ys 
append (C x xs) ys = x `C` (append xs ys)


{-@ reflect chunk @-}
{-@ chunk :: i:Int -> xs:List a -> {v:List (List a) | if (i <= 1 || llen xs <= i) then (llen v == 1) else (llen v < llen xs) } / [llen xs] @-}
chunk :: Int -> List a -> List (List a)
chunk i xs 
  | i <= 1
  = C xs N 
  | llen xs <= i 
  = C xs N 
  | otherwise
  = C (take i xs) (chunk i (drop i xs))

{-@ reflect drop @-}
{-@ drop :: i:Nat -> xs:{List a | i <= llen xs } -> {v:List a | llen v == llen xs - i } @-} 
drop :: Int -> List a -> List a 
drop i N = N 
drop i (C x xs)
  | i == 0 
  = C x xs  
  | otherwise 
  = drop (i-1) xs 

{-@ reflect take @-}
{-@ take :: i:Nat -> xs:{List a | i <= llen xs } -> {v:List a | llen v == i} @-} 
take :: Int -> List a -> List a 
take i N = N 
take i (C x xs)
  | i == 0 
  = N  
  | otherwise 
  = C x (take (i-1) xs)


-------------------------------------------------------------------------------
----------  String Chunking ---------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect chunkString @-}
{-@ chunkString :: Int -> xs:SMTString -> List (SMTString) / [stringLen xs] @-}
chunkString :: Int -> SMTString -> List (SMTString)
chunkString i xs 
  | i <= 1
  = C xs N 
  | stringLen xs <= i 
  = C xs N 
  | otherwise
  = C (takeString i xs) (chunkString i (dropString i xs))


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
------------ Liquid Proofs Start HERE -----------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------


-------------------------------------------------------------------------------
----------  Proof that toMI distributes ---------------------------------------
-------------------------------------------------------------------------------

{-@ distributionOfMI :: MI target -> is:SMTString -> n:Int -> {toMI is == mconcat (map toMI (chunkString n is))} @-}

distributionOfMI :: forall (target :: Symbol). (KnownSymbol target) => MI target -> SMTString -> Int -> Proof
distributionOfMI _ is n = distributeInput (toMI :: SMTString -> MI target) (distributestoMI (mempty :: MI target)) is n 


{-@ distributeInput
     :: f:(SMTString -> MI target)
     -> thm:(x1:SMTString -> x2:SMTString -> {f (concatString x1 x2) == mappend (f x1) (f x2)} )
     -> is:SMTString
     -> n:Int 
     -> {f is == mconcat (map f (chunkString n is))}
     / [stringLen is] 
  @-}

distributeInput :: forall (target :: Symbol). (KnownSymbol target) 
  => (SMTString -> MI target)
  -> (SMTString -> SMTString -> Proof)
  -> SMTString -> Int -> Proof
distributeInput f thm is n  
  | stringLen is <= n || n <= 1
  =   mconcat (map f (chunkString n is))
  ==. mconcat (map f (C is N))
  ==. mconcat (f is `C` map f N)
  ==. mconcat (f is `C` N)
  ==. mappend (f is) (mconcat N)
  ==. mappend (f is) (mempty :: MI target)
  ==. f is ? mempty_left (f is)
  *** QED 
  | otherwise
  =   mconcat (map f (chunkString n is))
  ==. mconcat (map f (C (takeString n is) (chunkString n (dropString n is)))) 
  ==. mconcat (f (takeString n is) `C` map f (chunkString n (dropString n is)))
  ==. mappend (f (takeString n is)) (mconcat (map f (chunkString n (dropString n is))))
  ==. mappend (f (takeString n is)) (f (dropString n is))
       ? distributeInput f thm (dropString n is) n  
  ==. f (concatString (takeString n is) (dropString n is))
       ? thm (takeString n is) (dropString n is)
  ==. f is 
       ? concatTakeDrop n is 
  *** QED 



distributestoMI :: forall (target :: Symbol). (KnownSymbol target) => MI target -> SMTString -> SMTString -> Proof 
{-@ distributestoMI :: MI target -> x1:SMTString -> x2:SMTString -> {toMI (concatString x1 x2) == mappend (toMI x1) (toMI x2)} @-} 
distributestoMI _ x1 x2
  | stringLen x1 == 0, stringLen x2 == 0 
  =   mappend (toMI x1) (toMI x2)
  ==. mappend (mempty :: MI target) (mempty :: MI target)
       ? mempty_left (mempty :: MI target) 
  ==. (mempty :: MI target)
  ==. toMI (concatString x1 x2)
  *** QED 

distributestoMI _ x1 x2
  | stringLen x1 == 0 
  =   mappend (toMI x1) (toMI x2)
  ==. mappend (mempty :: MI target) (toMI x2 :: MI target)
  ==. toMI x2 
      ? mempty_right (toMI x2 :: MI target)
  ==. toMI (concatString x1 x2)
      ? concatEmpLeft x1 x2 
  *** QED 

distributestoMI _ x1 x2
  | stringLen x2 == 0 
  =   mappend (toMI x1) (toMI x2)
  ==. mappend (toMI x1) (mempty :: MI target)
  ==. (toMI x1 :: MI target)
      ? mempty_left (toMI x1 :: MI target)
  ==. toMI (concatString x1 x2)
      ? concatEmpRight x1 x2 
  *** QED 

distributestoMI _ x1 x2 
  | stringLen (fromString (symbolVal (Proxy :: Proxy target))) < 2 
  =   let tg = (fromString (symbolVal (Proxy :: Proxy target))) in 
      mappend (toMI x1 :: MI target) (toMI x2 :: MI target)  
  ==. mappend (MI x1 (makeIndices x1 tg 0 (stringLen x1 - 1)))
              (MI x2 (makeIndices x2 tg 0 (stringLen x2 - 1)))
  ==. MI (concatString x1 x2)
         ((castGoodIndexRightList tg x1 x2 (makeIndices x1 tg 0 (stringLen x1 - 1))
          `append`
           makeNewIndices x1 x2 tg
          ) `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
  ==. MI (concatString x1 x2)
         ((castGoodIndexRightList tg x1 x2 (makeIndices x1 tg 0 (stringLen x1 - 1))
          `append`
           N
          ) `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
  ==. MI (concatString x1 x2)
         (castGoodIndexRightList tg x1 x2 (makeIndices x1 tg 0 (stringLen x1 - 1))
           `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
      ? appendNil (castGoodIndexRightList tg x1 x2 (makeIndices x1 tg 0 (stringLen x1 - 1)))
  ==. MI (concatString x1 x2)
         (castGoodIndexRightList tg x1 x2 (makeIndices x1 tg 0 (stringLen x1 - 1))
           `append`
          (makeIndices (concatString x1 x2) tg (stringLen x1) (stringLen x1 + stringLen x2 -1))) 
      ? shiftIndexesRight' 0 (stringLen x2 - 1) x1 x2 tg 
  ==. MI (concatString x1 x2)
         ( (makeIndices (concatString x1 x2) tg 0 (stringLen x1 - 1))
           `append`
          (makeIndices (concatString x1 x2) tg (stringLen x1) (stringLen x1 + stringLen x2 -1))) 
      ? (concatmakeNewIndices 0 (stringLen x1 -1) tg x1 x2) 
  ==. MI (concatString x1 x2)
         (makeIndices (concatString x1 x2) tg 0 (stringLen x1 - 1)
           `append`
          makeIndices (concatString x1 x2) tg (stringLen x1) (stringLen x1 + stringLen x2 -1)) 
  ==. MI (concatString x1 x2)
         (makeIndices (concatString x1 x2) tg 0 (stringLen x1 - 1)
           `append`
          makeIndices (concatString x1 x2) tg (stringLen x1) (stringLen (concatString x1 x2) -1)) 
  ==. MI (concatString x1 x2) 
         (makeIndices (concatString x1 x2) tg 0 (stringLen (concatString x1 x2) - 1))
      ? mergeIndices (concatString x1 x2) tg 0 (stringLen x1 -1) (stringLen (concatString x1 x2) - 1) 
  ==. toMI (concatString x1 x2)
  *** QED 

distributestoMI _ x1 x2
  | 0 <= stringLen x1 - stringLen (fromString (symbolVal (Proxy :: Proxy target))) 
  =   let tg = (fromString (symbolVal (Proxy :: Proxy target))) in 
      mappend (toMI x1 :: MI target) (toMI x2:: MI target)  
  ==. mappend (MI x1 (makeIndices x1 tg 0 (stringLen x1 - 1)))
              (MI x2 (makeIndices x2 tg 0 (stringLen x2 - 1)))
  ==. MI (concatString x1 x2)
         ((castGoodIndexRightList tg x1 x2 (makeIndices x1 tg 0 (stringLen x1 - 1))
          `append`
           makeNewIndices x1 x2 tg
          ) `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
  ==. MI (concatString x1 x2)
         ((castGoodIndexRightList tg x1 x2 (makeIndices x1 tg 0 (stringLen x1 - 1))
          `append`
           makeIndices (concatString x1 x2) tg (maxInt (stringLen x1 - stringLen tg +1) 0) (stringLen x1 -1)
          ) `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
  ==. MI (concatString x1 x2)
         ((castGoodIndexRightList tg x1 x2 (makeIndices x1 tg 0 (stringLen x1 - 1))
          `append`
           makeIndices (concatString x1 x2) tg (stringLen x1 - stringLen tg +1) (stringLen x1 -1)
          ) `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
  ==. MI (concatString x1 x2)
         ((makeIndices (concatString x1 x2) tg 0 (stringLen x1 - stringLen tg)
          `append`
           makeIndices (concatString x1 x2) tg (stringLen x1 - stringLen tg +1) (stringLen x1 -1)
          ) `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
         ? catIndices x1 x2 tg 0 (stringLen x1 -1 ) -- HERE HERE requires stringLen tg <= stringLen x1
  ==. MI (concatString x1 x2)
         ((makeIndices (concatString x1 x2) tg 0 (stringLen x1 - stringLen tg)
          `append`
           makeIndices (concatString x1 x2) tg (stringLen x1 - stringLen tg +1) (stringLen x1 -1)
          ) `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
  ==. MI (concatString x1 x2)
         (makeIndices (concatString x1 x2) tg 0 (stringLen x1 -1)
         `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
          ? mergeIndices (concatString x1 x2) tg 0 (stringLen x1 -stringLen tg) (stringLen x1-1)
  ==. MI (concatString x1 x2)
         (makeIndices (concatString x1 x2) tg 0 (stringLen x1 -1)
         `append`
          makeIndices (concatString x1 x2) tg (stringLen x1) (stringLen x1 + stringLen x2 - 1))
          ? shiftIndexesRight' 0 (stringLen x2 -1) x1 x2 tg 
  ==. MI (concatString x1 x2)
         (makeIndices (concatString x1 x2) tg 0 (stringLen x1 -1)
         `append`
          makeIndices (concatString x1 x2) tg (stringLen x1) (stringLen (concatString x1 x2) - 1))
  ==. MI (concatString x1 x2) 
         (makeIndices (concatString x1 x2) tg 0 (stringLen (concatString x1 x2) - 1))
          ? mergeIndices (concatString x1 x2) tg 0 (stringLen x1- 1) (stringLen (concatString x1 x2) - 1)
  ==. toMI (concatString x1 x2)
  *** QED 
distributestoMI _ x1 x2
  | stringLen x1 - stringLen (fromString (symbolVal (Proxy :: Proxy target))) < 0 
  =   let tg = (fromString (symbolVal (Proxy :: Proxy target))) in 
      mappend (toMI x1 :: MI target) (toMI x2:: MI target)  
  ==. mappend (MI x1 (makeIndices x1 tg 0 (stringLen x1 - 1)))
              (MI x2 (makeIndices x2 tg 0 (stringLen x2 - 1)))
  ==. MI (concatString x1 x2)
         ((castGoodIndexRightList tg x1 x2 (makeIndices x1 tg 0 (stringLen x1 - 1))
          `append`
           makeNewIndices x1 x2 tg
          ) `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
  ==. MI (concatString x1 x2)
         ((castGoodIndexRightList tg x1 x2 (makeIndices x1 tg 0 (stringLen x1 - 1))
          `append`
           makeIndices (concatString x1 x2) tg (maxInt (stringLen x1 - stringLen tg +1) 0) (stringLen x1 -1)
          ) `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
  ==. MI (concatString x1 x2)
         ((castGoodIndexRightList tg x1 x2 (makeIndices x1 tg 0 (stringLen x1 - 1))
          `append`
           makeIndices (concatString x1 x2) tg 0 (stringLen x1 -1)
          ) `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
          
  ==. MI (concatString x1 x2)
         ((N
          `append`
           makeIndices (concatString x1 x2) tg 0 (stringLen x1 -1)
          ) `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
         ? makeNewIndicesNullSmallInput x1 tg 0 (stringLen x1 - 1)  
  ==. MI (concatString x1 x2)
         (makeIndices (concatString x1 x2) tg 0 (stringLen x1 -1)
           `append`
          (map (shiftStringRight tg x1 x2) (makeIndices x2 tg 0 (stringLen x2 - 1)))) 
  ==. MI (concatString x1 x2)
         (makeIndices (concatString x1 x2) tg 0 (stringLen x1 -1)
         `append`
          makeIndices (concatString x1 x2) tg (stringLen x1) (stringLen x1 + stringLen x2 - 1))
          ? shiftIndexesRight' 0 (stringLen x2 -1) x1 x2 tg 
  ==. MI (concatString x1 x2)
         (makeIndices (concatString x1 x2) tg 0 (stringLen x1 -1)
         `append`
          makeIndices (concatString x1 x2) tg (stringLen x1) (stringLen (concatString x1 x2) - 1))
  ==. MI (concatString x1 x2) 
         (makeIndices (concatString x1 x2) tg 0 (stringLen (concatString x1 x2) - 1))
          ? mergeIndices (concatString x1 x2) tg 0 (stringLen x1- 1) (stringLen (concatString x1 x2) - 1)
  ==. toMI (concatString x1 x2)
  *** QED 

-------------------------------------------------------------------------------
----------  Parallelization: pmconcat i is == mconcat is ----------------------
-------------------------------------------------------------------------------

pmconcatEquivalence :: forall (target :: Symbol). (KnownSymbol target) => Int -> List (MI target) -> Proof
{-@ pmconcatEquivalence :: i:Int -> is:List (MI target) -> {pmconcat i is == mconcat is} / [llen is] @-}
pmconcatEquivalence i is 
  | i <= 1
  = pmconcat i is ==. mconcat is *** QED 
pmconcatEquivalence i N 
  =   pmconcat i N 
  ==. (mempty :: MI target) 
  ==. mconcat N 
  *** QED 
pmconcatEquivalence i (C x N) 
  =   pmconcat i (C x N)
  ==. x 
  ==. mappend x mempty 
      ? mempty_left x
  ==. mappend x (mconcat N) 
  ==. mconcat (C x N) 
  *** QED 
pmconcatEquivalence i xs 
  | llen xs <= i 
  =   pmconcat i xs 
  ==. pmconcat i (map mconcat (chunk i xs))
  ==. pmconcat i (map mconcat (C xs N))
  ==. pmconcat i (mconcat xs `C`  map mconcat N)
  ==. pmconcat i (mconcat xs `C`  N)
  ==. mconcat xs
  *** QED 
pmconcatEquivalence i xs
  =   pmconcat i xs 
  ==. pmconcat i (map mconcat (chunk i xs))
  ==. mconcat (map mconcat (chunk i xs))
       ? pmconcatEquivalence i (map mconcat (chunk i xs))
  ==. mconcat xs
       ? mconcatAssoc i xs
  *** QED 

-- | Monoid implications 

mconcatAssocOne :: forall (target :: Symbol). (KnownSymbol target) => Int -> List (MI target) -> Proof 
{-@ mconcatAssocOne :: i:Nat -> xs:{List (MI target) | i <= llen xs} 
     -> {mconcat xs == mappend (mconcat (take i xs)) (mconcat (drop i xs))}
     /[i]
  @-} 
mconcatAssocOne i N 
  =   mappend (mconcat (take i N)) (mconcat (drop i N)) 
  ==. mappend (mconcat N) (mconcat N)
  ==. mappend (mempty :: MI target) (mempty :: MI target)
  ==. (mempty :: MI target) 
      ? mempty_left  (mempty :: MI target)
  ==. mconcat N 
  *** QED 

mconcatAssocOne i (C x xs)
  | i == 0
  =   mappend (mconcat (take i (C x xs))) (mconcat (drop i (C x xs))) 
  ==. mappend (mconcat N) (mconcat (C x xs))
  ==. mappend mempty (mconcat (C x xs))
  ==. mconcat (C x xs)
      ? mempty_right (mconcat (C x xs))
  *** QED 
  | otherwise    
  =   mappend (mconcat (take i (C x xs))) (mconcat (drop i (C x xs))) 
  ==. mappend (mconcat (C x (take (i-1) xs))) (mconcat (drop (i-1) xs))
  ==. mappend (mappend x (mconcat (take (i-1) xs))) (mconcat (drop (i-1) xs))
       ? mappend_assoc x (mconcat (take (i-1) xs)) (mconcat (drop (i-1) xs))
  ==. mappend x (mappend (mconcat (take (i-1) xs)) (mconcat (drop (i-1) xs)))
       ? mconcatAssocOne (i-1) xs
  ==. mappend x (mconcat xs)
  ==. mconcat (C x xs)
  *** QED 

-- Generalization to chunking  

mconcatAssoc :: forall (target :: Symbol). (KnownSymbol target) => Int -> List (MI target) -> Proof 
{-@ mconcatAssoc :: i:Int -> xs:List (MI target) 
  -> { mconcat xs == mconcat (map mconcat (chunk i xs))}
  /  [llen xs] @-}
mconcatAssoc i xs  
  | i <= 1 || llen xs <= i
  =   mconcat (map mconcat (chunk i xs))
  ==. mconcat (map mconcat (C xs N))
  ==. mconcat (mconcat xs `C` map mconcat N)
  ==. mconcat (mconcat xs `C` N)
  ==. mappend (mconcat xs) (mconcat N)
  ==. mappend (mconcat xs) (mempty :: MI target)
  ==. mconcat xs 
       ? mempty_left (mconcat xs)
  *** QED  
   | otherwise
   =   mconcat (map mconcat (chunk i xs))
   ==. mconcat (map mconcat (take i xs `C` chunk i (drop i xs)))
   ==. mconcat (mconcat (take i xs) `C` map mconcat (chunk i (drop i xs)))
   ==. mappend (mconcat (take i xs)) (mconcat (map mconcat (chunk i (drop i xs))))
   ==. mappend (mconcat (take i xs)) (mconcat (drop i xs))
        ? mconcatAssoc i (drop i xs)
   ==. mconcat xs 
        ? mconcatAssocOne i xs 
   *** QED 


-------------------------------------------------------------------------------
----------  Proof that MI is a Monoid -----------------------------------------
-------------------------------------------------------------------------------

mempty_left :: forall (target :: Symbol). (KnownSymbol target) => MI target -> Proof
{-@ mempty_left :: xs:MI target -> {mappend xs mempty == xs } @-}
mempty_left (MI i1 is1) 
  = let tg = fromString (symbolVal (Proxy :: Proxy target)) in 
      mappend (MI i1 is1) (mempty :: MI target)
  ==. mappend (MI i1 is1) (MI stringEmp N) 
  ==. MI (concatString i1 stringEmp)
         ((castGoodIndexRightList tg i1 stringEmp is1
            `append`
           makeNewIndices i1 stringEmp tg 
         ) `append`
         (map (shiftStringRight tg i1 stringEmp) N))
      ? concatStringNeutralLeft i1 
        -- NV ordering is important! 
        -- concatString i1 stringEmp == i1 should come before application of MI
  ==. MI i1
         ((castGoodIndexRightList tg i1 stringEmp is1
            `append`
           makeNewIndices i1 stringEmp tg
         ) `append`
         (map (shiftStringRight tg i1 stringEmp) N))
  ==. MI i1 ((is1 `append` N) `append` (map (shiftStringRight tg i1 stringEmp) N))
      ? makeNewIndicesNullLeft i1 tg 
  ==. MI i1 (is1 `append` map (shiftStringRight tg i1 stringEmp) N)
      ? appendNil is1  
  ==. MI i1 (is1 `append` N)
      ? appendNil is1  
  ==. MI i1 is1 
  *** QED 

mempty_right :: forall (target :: Symbol). (KnownSymbol target) => MI target -> Proof
{-@ mempty_right :: xs:MI target -> {mappend mempty xs == xs } @-}
mempty_right (MI i is)
  =   let tg = (fromString (symbolVal (Proxy :: Proxy target))) in 
      mappend (mempty :: MI target) (MI i is) 
  ==. mappend (MI stringEmp N) (MI i is) 
  ==. MI (concatString stringEmp i)
       ((castGoodIndexRightList tg stringEmp i N
          `append`
        makeNewIndices stringEmp i tg 
       ) `append`
       (map (shiftStringRight tg stringEmp i) is)) 
       ? concatStringNeutralRight i
  ==. MI i
        ((N`append` makeNewIndices stringEmp i tg
        ) `append`
        (map (shiftStringRight tg stringEmp i) is)) 
  ==. MI i
       (makeNewIndices stringEmp i tg
        `append`
       (map (shiftStringRight tg stringEmp i) is)) 
  ==. MI i (N `append` (map (shiftStringRight tg stringEmp i) is)) 
       ? makeNewIndicesNullRight i tg
  ==. MI i (map (shiftStringRight tg stringEmp i) is)
       ? mapShiftZero tg i is 
  ==. MI i is 
  *** QED 

{-@ mappend_assoc :: x:MI target -> y:MI target -> z:MI target
  -> { mappend x (mappend y z) = mappend (mappend x y) z}
  @-}
mappend_assoc 
     :: forall (target :: Symbol). (KnownSymbol target) 
     => MI target ->  MI target ->  MI target -> Proof
mappend_assoc x@(MI xi xis) y@(MI yi yis) z@(MI zi zis)
  | stringLen (fromString (symbolVal (Proxy :: Proxy target))) <= stringLen yi 
  = let tg = (fromString (symbolVal (Proxy :: Proxy target))) in 
      mappend x (mappend y z)
  ==. mappend (MI xi xis) (mappend (MI yi yis) (MI zi zis))
  ==. mappend (MI xi xis) 
              (MI (concatString yi zi)
                  ((castGoodIndexRightList tg yi zi yis
                     `append`
                   makeNewIndices yi zi tg
                   ) `append`
                  (map (shiftStringRight tg yi zi) zis)))
  ==. MI (concatString xi (concatString yi zi))
         ((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          (map (shiftStringRight tg xi (concatString yi zi)) ((castGoodIndexRightList tg yi zi yis
                     `append`
                   makeNewIndices yi zi tg
                   ) `append`
                  (map (shiftStringRight tg yi zi) zis))))
      ? concatStringAssoc xi yi zi 
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          (map (shiftStringRight tg xi (concatString yi zi)) ((castGoodIndexRightList tg yi zi yis
                     `append`
                   makeNewIndices yi zi tg
                   ) `append`
                  (map (shiftStringRight tg yi zi) zis))))
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          (map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis
                     `append`
                   makeNewIndices yi zi tg
                   ))
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
      ? mapAppend (shiftStringRight tg xi (concatString yi zi))
                  (castGoodIndexRightList tg yi zi yis
                     `append`
                   makeNewIndices yi zi tg
                   )
                   (map (shiftStringRight tg yi zi) zis)
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          (map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis)
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)
           )
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
      ? mapAppend (shiftStringRight tg xi (concatString yi zi))
                  (castGoodIndexRightList tg yi zi yis)
                  (makeNewIndices yi zi tg)
-- ((x1~x2) ~ (x3~x4)) ~ x5
-- == 
-- (x1~x2) ~ x3 ~ x4 ~ x5 

  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis))
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)
           )
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
      ? appendReorder (castGoodIndexRightList tg xi (concatString yi zi) xis)
                      (makeNewIndices xi (concatString yi zi) tg)
                      (map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis))
                      (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg))
                      (map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))

  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis) 
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis))
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)
           )
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
      ? castConcat tg xi yi zi xis 
  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)
           `append`
           castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
          ) `append`
          map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis))
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)
           )
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
      ? shiftIndexesLeft xi yi zi tg 
  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)
           `append`
           castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
          ) `append`
          castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis))
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)
           )
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
         ? castEq3 tg xi yi zi yis 
  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)
           `append`
           castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
          ) `append`
          castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis))
            `append`
           makeNewIndices (concatString xi yi) zi tg
           )
            `append`
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
         ? shiftIndexesRight xi yi zi tg 
  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)
           `append`
           castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
          ) `append`
          castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis))
            `append`
           makeNewIndices (concatString xi yi) zi tg
           )
            `append`
           map (shiftStringRight tg (concatString xi yi) zi) zis)
         ? mapLenFusion tg xi yi zi zis 
  ==. MI (concatString (concatString xi yi) zi)
         (((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)
              `append`
           castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
           ) `append`
           castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis)
            `append`
          makeNewIndices (concatString xi yi) zi tg
          ) `append`
         (map (shiftStringRight tg (concatString xi yi) zi) zis)) 
        ? castAppend tg (concatString xi yi) zi 
                     (castGoodIndexRightList tg xi yi xis)
                     (makeNewIndices xi yi tg)
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis
              `append`
            makeNewIndices xi yi tg
           ) `append`
           castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis)
            `append`
          makeNewIndices (concatString xi yi) zi tg
         ) `append`
         (map (shiftStringRight tg (concatString xi yi) zi) zis)) 
        ? castAppend tg (concatString xi yi) zi 
             (castGoodIndexRightList tg xi yi xis
              `append`
             makeNewIndices xi yi tg
             )
             (map (shiftStringRight tg xi yi) yis)
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg (concatString xi yi) zi ((castGoodIndexRightList tg xi yi xis
              `append`
            makeNewIndices xi yi tg
           ) `append`
           (map (shiftStringRight tg xi yi) yis))
            `append`
          makeNewIndices (concatString xi yi) zi tg
         ) `append`
         (map (shiftStringRight tg (concatString xi yi) zi) zis)) 
  ==. mappend (
        MI (concatString xi yi)
           ((castGoodIndexRightList tg xi yi xis
              `append`
            makeNewIndices xi yi tg
           ) `append`
           (map (shiftStringRight tg xi yi) yis))) (MI zi zis) 
  ==. mappend (mappend (MI xi xis) (MI yi yis)) (MI zi zis)
  *** QED 

mappend_assoc x@(MI xi xis) y@(MI yi yis) z@(MI zi zis)
  | stringLen yi < stringLen (fromString (symbolVal (Proxy :: Proxy target))) 
  = let tg = (fromString (symbolVal (Proxy :: Proxy target))) in 
      mappend x (mappend y z)
  ==. mappend (MI xi xis) (mappend (MI yi yis) (MI zi zis))
  ==. mappend (MI xi xis) 
              (MI (concatString yi zi)
                  ((castGoodIndexRightList tg yi zi yis
                     `append`
                   makeNewIndices yi zi tg
                   ) `append`
                  (map (shiftStringRight tg yi zi) zis)))
  ==. MI (concatString xi (concatString yi zi))
         ((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          (map (shiftStringRight tg xi (concatString yi zi)) ((castGoodIndexRightList tg yi zi yis
                     `append`
                   makeNewIndices yi zi tg
                   ) `append`
                  (map (shiftStringRight tg yi zi) zis))))
      ? concatStringAssoc xi yi zi 
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          (map (shiftStringRight tg xi (concatString yi zi)) ((castGoodIndexRightList tg yi zi yis
                     `append`
                   makeNewIndices yi zi tg
                   ) `append`
                  (map (shiftStringRight tg yi zi) zis))))
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          (map (shiftStringRight tg xi (concatString yi zi)) ((castGoodIndexRightList tg yi zi N
                     `append`
                   makeNewIndices yi zi tg
                   ) `append`
                  (map (shiftStringRight tg yi zi) zis))))
        ? emptyIndices y yis
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          (map (shiftStringRight tg xi (concatString yi zi)) (
                   makeNewIndices yi zi tg
                   `append`
                  (map (shiftStringRight tg yi zi) zis))))
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg xi (concatString yi zi) xis
           `append`
           makeNewIndices xi (concatString yi zi) tg
          ) `append`
          (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg) 
             `append` 
           map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis)))
      ? mapAppend (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg) (map (shiftStringRight tg yi zi) zis)
  ==. MI (concatString (concatString xi yi) zi)
         (((castGoodIndexRightList tg xi (concatString yi zi) xis)
           `append`
           ((makeNewIndices xi (concatString yi zi) tg)
           `append`
           (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg))))
            `append`
           (map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis)))
      ? appendGroupNew (castGoodIndexRightList tg xi (concatString yi zi) xis)
                       (makeNewIndices xi (concatString yi zi) tg)
                       (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg))
                       (map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
  ==. MI (concatString (concatString xi yi) zi)
         ( (castGoodIndexRightList tg xi (concatString yi zi) xis)
           `append`
           ((castGoodIndexRightList tg (concatString xi yi) zi ((makeNewIndices xi yi) tg))
           `append`
           (makeNewIndices (concatString xi yi) zi tg))
            `append`
           (map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis)))
      ? shiftNewIndices xi yi zi tg 
  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg xi (concatString yi zi) xis)
           `append`
           (castGoodIndexRightList tg (concatString xi yi) zi ((makeNewIndices xi yi) tg)))
           `append`
           (makeNewIndices (concatString xi yi) zi tg))
            `append`
           (map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis)))
      ? appendUnGroupNew (castGoodIndexRightList tg xi (concatString yi zi) xis)
                         (castGoodIndexRightList tg (concatString xi yi) zi ((makeNewIndices xi yi) tg))
                         (makeNewIndices (concatString xi yi) zi tg)
                         (map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis))
  ==. MI (concatString (concatString xi yi) zi)
         ((((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis))
           `append`
           (castGoodIndexRightList tg (concatString xi yi) zi ((makeNewIndices xi yi) tg)))
           `append`
           (makeNewIndices (concatString xi yi) zi tg))
            `append`
           (map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis)))
      ? castConcat tg xi yi zi xis 
  ==. MI (concatString (concatString xi yi) zi)
         ( ((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)
            `append`
             castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
           )
            `append`
          makeNewIndices (concatString xi yi) zi tg
           ) `append`
         (map (shiftStringRight tg (concatString xi yi) zi) zis)) 
      ? mapLenFusion tg xi yi zi zis 
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis
              `append`
            makeNewIndices xi yi tg
           )
            `append`
          makeNewIndices (concatString xi yi) zi tg
           ) `append`
         (map (shiftStringRight tg (concatString xi yi) zi) zis)) 
      ? castAppend tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis) (makeNewIndices xi yi tg)
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg (concatString xi yi) zi ((castGoodIndexRightList tg xi yi xis
              `append`
            makeNewIndices xi yi tg
           ) `append`
           N)
            `append`
          makeNewIndices (concatString xi yi) zi tg
         ) `append`
         (map (shiftStringRight tg (concatString xi yi) zi) zis)) 
         ? appendNil (castGoodIndexRightList tg xi yi xis `append` makeNewIndices xi yi tg)
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg (concatString xi yi) zi ((castGoodIndexRightList tg xi yi xis
              `append`
            makeNewIndices xi yi tg
           ) `append`
           (map (shiftStringRight tg xi yi) N))
            `append`
          makeNewIndices (concatString xi yi) zi tg
         ) `append`
         (map (shiftStringRight tg (concatString xi yi) zi) zis)) 
  ==. MI (concatString (concatString xi yi) zi)
         ((castGoodIndexRightList tg (concatString xi yi) zi ((castGoodIndexRightList tg xi yi xis
              `append`
            makeNewIndices xi yi tg
           ) `append`
           (map (shiftStringRight tg xi yi) yis))
            `append`
          makeNewIndices (concatString xi yi) zi tg
         ) `append`
         (map (shiftStringRight tg (concatString xi yi) zi) zis)) 
         ? emptyIndices y yis 
  ==. mappend (
        MI (concatString xi yi)
           ((castGoodIndexRightList tg xi yi xis
              `append`
            makeNewIndices xi yi tg
           ) `append`
           (map (shiftStringRight tg xi yi) yis))) (MI zi zis) 
  ==. mappend (mappend (MI xi xis) (MI yi yis)) (MI zi zis)
  *** QED 

-------------------------------------------------------------------------------
----------  Lemmata on Casts --------------------------------------------------
-------------------------------------------------------------------------------

{-@ castAppend :: target:SMTString -> input:SMTString -> x:SMTString 
     -> is1:List (GoodIndex input target) 
     -> is2:List (GoodIndex input target) -> 
   {castGoodIndexRightList target input x (append is1 is2) == append (castGoodIndexRightList target input x is1) (castGoodIndexRightList target input x is2)}
    @-}
castAppend :: SMTString -> SMTString -> SMTString -> List Int -> List Int -> Proof 
castAppend target input x is1 is2 
  =   castGoodIndexRightList target input x (append is1 is2)
  ==. append is1 is2 
  ==. append (castGoodIndexRightList target input x is1) (castGoodIndexRightList target input x is2)
  *** QED 

castConcat :: SMTString -> SMTString -> SMTString -> SMTString -> List Int -> Proof
{-@ castConcat :: tg:SMTString -> xi:SMTString -> yi:SMTString -> zi:SMTString 
             ->  xis:List (GoodIndex xi tg) 
        -> {castGoodIndexRightList tg xi (concatString yi zi) xis == castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)} @-}
castConcat tg xi yi zi xis 
  =   castGoodIndexRightList tg xi (concatString yi zi) xis
  ==. xis 
  ==. castGoodIndexRightList tg xi yi xis
  ==. castGoodIndexRightList tg (concatString xi yi) zi (castGoodIndexRightList tg xi yi xis)
  *** QED 


castEq3 :: SMTString -> SMTString -> SMTString -> SMTString -> List Int -> Proof
{-@ castEq3 :: tg:SMTString -> xi:SMTString -> yi:SMTString -> zi:SMTString 
             ->  yis:List (GoodIndex yi tg) 
        -> {castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis) == map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis)} @-}
castEq3 tg xi yi zi yis 
  =   castGoodIndexRightList tg (concatString xi yi) zi (map (shiftStringRight tg xi yi) yis)
  ==. map (shiftStringRight tg xi yi) yis 
  ==. map (shiftStringRight tg xi (concatString yi zi)) (castGoodIndexRightList tg yi zi yis)
        ? mapShiftIndex tg xi yi zi yis 
  *** QED 


-------------------------------------------------------------------------------
----------  Lemmata on Lists --------------------------------------------------
-------------------------------------------------------------------------------

{-@ appendNil :: xs:List a -> { append xs N = xs } @-} 
appendNil :: List a -> Proof 
appendNil N 
  =   append N N
  ==. N
  *** QED 
appendNil (C x xs) 
  =   append (C x xs) N
  ==. C x (append xs N)
  ==. C x xs ? appendNil xs 
  *** QED 

-- (x1 ~ x2) ~ (x3 ~ x4)
-- == 
-- ((x1 ~ (x2 ~ x3)) ~ x4)


appendGroupNew :: List a -> List a -> List a -> List a -> Proof
{-@ appendGroupNew 
  :: x1:List a 
  -> x2:List a 
  -> x3:List a 
  -> x4:List a 
  -> {   (append (append x1 x2) (append x3 x4))
      == (append (append x1 (append x2 x3)) x4)
     } @-}
appendGroupNew x1 x2 x3 x4 
  =   (append (append x1 x2) (append x3 x4))
  ==. (append (append (append x1 x2) x3) x4)
      ? appendAssoc (append x1 x2) x3 x4  
  ==. (append (append x1 (append x2 x3)) x4)
      ? appendAssoc x1 x2 x3
  *** QED 



-- (x1 ~ (x2 ~ x3)) ~ x4 == ((x1 ~ x2) ~ x3) ~ x4

appendUnGroupNew :: List a -> List a -> List a -> List a -> Proof
{-@ appendUnGroupNew 
  :: x1:List a 
  -> x2:List a 
  -> x3:List a 
  -> x4:List a 
  -> {   ((append (append (append x1 x2) x3) x4))
      == (append (append x1 (append x2 x3)) x4)
     } @-}
appendUnGroupNew x1 x2 x3 x4 
  =   append (append (append x1 x2) x3) x4
  ==. append (append x1 (append x2 x3)) x4
      ? appendAssoc x1 x2 x3 
  *** QED 



appendReorder :: List a -> List a -> List a -> List a -> List a -> Proof
{-@ appendReorder 
  :: x1:List a 
  -> x2:List a 
  -> x3:List a 
  -> x4:List a 
  -> x5:List a 
  -> {   (append (append x1 x2) (append (append x3 x4) x5))
      == (append (append (append (append x1 x2) x3) x4) x5)
     } @-}
appendReorder x1 x2 x3 x4 x5 
  =   append (append x1 x2) (append (append x3 x4) x5)
  ==. append (append x1 x2) (append x3 (append x4 x5))
       ? appendAssoc x3 x4 x5 
  ==. append (append (append x1 x2) x3) (append x4 x5)
      ? appendAssoc (append x1 x2) x3 (append x4 x5) 
  ==. append ((append (append (append x1 x2) x3)) x4) x5
      ? appendAssoc (append (append x1 x2) x3) x4 x5 
  *** QED 

{-@ appendAssoc :: x:List a -> y:List a -> z:List a 
     -> {(append x (append y z)) == (append (append x y) z) } @-}
appendAssoc :: List a -> List a -> List a -> Proof
appendAssoc N y z 
  =   append N (append y z)
  ==. append y z
  ==. append (append N y) z
  *** QED 
appendAssoc (C x xs) y z
  =   append (C x xs) (append y z) 
  ==. C x (append xs (append y z))
  ==. C x (append (append xs y) z)
        ? appendAssoc xs y z
  ==. append (C x (append xs y)) z
  ==. append (append (C x xs) y) z
  *** QED 


mapAppend :: (a -> b) -> List a -> List a -> Proof
{-@ mapAppend 
     :: f:(a -> b) -> xs:List a -> ys:List a 
     -> {map f (append xs ys) == append (map f xs) (map f ys)}
  @-}
mapAppend f N ys 
  =   map f (append N ys)
  ==. map f ys 
  ==. append N (map f ys)
  ==. append (map f N) (map f ys)
  *** QED 
mapAppend f (C x xs) ys 
  =   map f (append (C x xs) ys)
  ==. map f (x `C` (append xs ys))
  ==. f x `C` (map f (append xs ys))
  ==. f x `C` (append (map f xs) (map f ys))
      ? mapAppend f xs ys 
  ==. append (f x `C` map f xs) (map f ys)
  ==. append (map f (x `C` xs)) (map f ys)
  *** QED 


-------------------------------------------------------------------------------
----------  Lemmata on Empty Indices ------------------------------------------
-------------------------------------------------------------------------------

emptyIndices :: forall (target :: Symbol). (KnownSymbol target) => MI target -> List Int  -> Proof
{-@ emptyIndices :: mi:MI target
                 -> is:{List (GoodIndex (inputMI mi) target) | is == indicesMI mi && stringLen (inputMI mi) < stringLen target}
                 -> { is == N } @-}
emptyIndices (MI _ _) N 
  = trivial 
emptyIndices (MI _ _) (C _ _)
  = trivial 

makeNewIndicesNullLeft :: SMTString -> SMTString -> Proof 
{-@ makeNewIndicesNullLeft 
  :: s:SMTString 
  -> t:SMTString 
  -> {makeNewIndices s stringEmp t == N } @-} 
makeNewIndicesNullLeft s t 
  | stringLen t < 2 
  = makeNewIndices s stringEmp t ==. N *** QED 
makeNewIndicesNullLeft  s t 
  | 1 + stringLen s <= stringLen t
  =   makeNewIndices s stringEmp t
  ==. makeIndices (concatString s stringEmp) t
                   (maxInt (1 + stringLen s - stringLen t)  0)
                   (stringLen s - 1)
  ==. makeIndices s t
                   0
                   (stringLen s - 1) 
                   ? concatStringNeutralLeft s
  ==. makeIndices s t
                   0
                   (stringLen s - 1)
  ==. N ? makeNewIndicesNullSmallInput s t 0 (stringLen s - 1)
  *** QED 
makeNewIndicesNullLeft s t 
  =   makeNewIndices s stringEmp t
  ==. makeIndices (concatString s stringEmp) t
                   (maxInt (1 + stringLen s - stringLen t)  0)
                   (stringLen s - 1)
  ==. makeIndices (concatString s stringEmp) t
                   (1 + stringLen s - stringLen t)
                   (stringLen s - 1)
  ==. makeIndices s t
                   (1 + stringLen s - stringLen t)
                   (stringLen s - 1) ? concatStringNeutralLeft s 
  ==. N ? makeNewIndicesNullSmallIndex s t (1 + stringLen s - stringLen t) (stringLen s - 1)
  *** QED 

makeNewIndicesNullSmallInput :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ makeNewIndicesNullSmallInput 
  :: s:SMTString 
  -> t:{SMTString | 1 + stringLen s <= stringLen t } 
  -> lo:Nat 
  -> hi:Int
  -> {makeIndices s t lo hi == N } / [hi - lo] @-} 
makeNewIndicesNullSmallInput s1 t lo hi
  | hi < lo 
  = makeIndices s1 t lo hi ==. N *** QED 
  | lo == hi, not (isGoodIndex s1 t lo)
  = makeIndices s1 t lo hi ==. N *** QED  
  | not (isGoodIndex s1 t lo)
  =   makeIndices s1 t lo hi
  ==. makeIndices s1 t (lo + 1) hi 
  ==. N ? makeNewIndicesNullSmallInput s1 t (lo+1) hi
  *** QED 


makeNewIndicesNullSmallIndex :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ makeNewIndicesNullSmallIndex 
  :: s:SMTString 
  -> t:{SMTString | stringLen t < 2 + stringLen s } 
  -> lo:{Nat | 1 + stringLen s - stringLen t <= lo  } 
  -> hi:{Int | lo <= hi}
  -> {makeIndices s t lo hi == N } / [hi - lo] @-} 
makeNewIndicesNullSmallIndex s1 t lo hi
  | lo == hi, not (isGoodIndex s1 t lo)
  = makeIndices s1 t lo hi ==. N *** QED  
  | not (isGoodIndex s1 t lo)
  =   makeIndices s1 t lo hi
  ==. makeIndices s1 t (lo + 1) hi 
  ==. N ? makeNewIndicesNullSmallIndex s1 t (lo+1) hi
  *** QED 


makeNewIndicesNullRight :: SMTString -> SMTString -> Proof 
{-@ makeNewIndicesNullRight 
  :: s1:SMTString 
  -> t:SMTString 
  -> {makeNewIndices stringEmp s1 t == N } @-} 
makeNewIndicesNullRight s t 
  | stringLen t < 2 
  = makeNewIndices stringEmp s t  ==. N *** QED 
makeNewIndicesNullRight s t 
  =   makeNewIndices stringEmp s t
  ==. makeIndices (concatString stringEmp s) t
                   (maxInt (1 + stringLen stringEmp - stringLen t) 0)
                   (stringLen stringEmp - 1)
  ==. makeIndices s t
                   (maxInt (1 - stringLen t) 0)
                   (-1)
      ? concatStringNeutralRight s 
  ==. makeIndices s t 0 (-1)
  ==. N  
  *** QED

-------------------------------------------------------------------------------
----------  Lemmata on Shifting Indices ---------------------------------------
-------------------------------------------------------------------------------

mapLenFusion :: SMTString -> SMTString -> SMTString -> SMTString -> List Int -> Proof
{-@ mapLenFusion :: tg:SMTString -> xi:SMTString -> yi:SMTString -> zi:SMTString 
            -> zis:List (GoodIndex zi tg) 
        -> {map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) zis) == map (shiftStringRight tg (concatString xi yi) zi) zis} 
        / [llen zis ] @-}
mapLenFusion tg xi yi zi N  
  =   map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) N)
  ==. map (shiftStringRight tg xi (concatString yi zi)) N 
  ==. N 
  ==. map (shiftStringRight tg (concatString xi yi) zi) N 
  *** QED  
mapLenFusion tg xi yi zi (C i is)  
  =   map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) (C i is))
  ==. map (shiftStringRight tg xi (concatString yi zi)) (shiftStringRight tg yi zi i `C` map (shiftStringRight tg yi zi) is)
  ==. shiftStringRight tg xi (concatString yi zi) (shiftStringRight tg yi zi i) `C` (map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) is))
  ==. shiftStringRight tg (concatString xi yi) zi i `C` (map (shiftStringRight tg xi (concatString yi zi)) (map (shiftStringRight tg yi zi) is))
  ==. shiftStringRight tg (concatString xi yi) zi i `C` (map (shiftStringRight tg (concatString xi yi) zi) is)
       ? mapLenFusion tg xi yi zi is 
  ==. map (shiftStringRight tg (concatString xi yi) zi) (C i is)
  *** QED  

{-@ shiftIndexesRight
  :: xi:SMTString 
  -> yi:SMTString 
  -> zi:SMTString 
  -> tg:{SMTString | stringLen tg <= stringLen yi } 
  -> { map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg) == makeNewIndices (concatString xi yi) zi tg }
  @-}
shiftIndexesRight :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexesRight xi yi zi tg
  | stringLen tg < 2 
  =   makeNewIndices (concatString xi yi) zi tg 
  ==. N
  ==. map (shiftStringRight tg xi (concatString yi zi)) N
  ==. map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)
  *** QED 
shiftIndexesRight xi yi zi tg
-- NV NV NV 
-- This is suspicious!!! it should require exactly the precondition 
-- || tg || <= || yi || 
--   | stringLen tg  <= stringLen yi + 1 
  =   makeNewIndices (concatString xi yi) zi tg  
  ==. makeIndices (concatString (concatString xi yi) zi) tg 
                   (maxInt (stringLen (concatString xi yi) - (stringLen tg -1)) 0)
                   (stringLen (concatString xi yi) - 1 )
  ==. makeIndices (concatString (concatString xi yi) zi) tg 
                   (stringLen (concatString xi yi) - (stringLen tg -1))
                   (stringLen (concatString xi yi) - 1 )
  ==. makeIndices (concatString (concatString xi yi) zi) tg 
                   (stringLen xi + stringLen yi - stringLen tg + 1)
                   (stringLen xi + stringLen yi - 1 )
  ==. makeIndices (concatString xi (concatString yi zi)) tg 
                   (stringLen xi + stringLen yi - stringLen tg + 1)
                   (stringLen xi + stringLen yi - 1 )
       ?concatStringAssoc xi yi zi
  ==. map (shiftStringRight tg xi (concatString yi zi)) (makeIndices (concatString yi zi) tg (stringLen yi - stringLen tg + 1) (stringLen yi - 1))
       ? shiftIndexesRight' (stringLen yi - stringLen tg + 1)
                            (stringLen yi - 1)
                            xi 
                            (concatString yi zi)
                            tg 
  ==. map (shiftStringRight tg xi (concatString yi zi)) 
               (makeIndices (concatString yi zi) tg 
                             (maxInt (stringLen yi - (stringLen tg -1)) 0)
                             (stringLen yi -1))
  ==. map (shiftStringRight tg xi (concatString yi zi)) 
          (makeNewIndices yi zi tg)
  *** QED

{-@ shiftIndexesRight'
  :: lo:Nat 
  -> hi:Int  
  -> x:SMTString 
  -> input:SMTString 
  -> target:SMTString
  -> { map (shiftStringRight target x input) (makeIndices input target lo hi) == makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi) }
  / [if hi < lo then 0 else  hi-lo]
  @-}
shiftIndexesRight' :: Int -> Int -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexesRight' lo hi x input target
  | hi < lo 
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) N
  ==. N
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
  *** QED 
  | lo == hi, isGoodIndex input target lo 
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (lo `C` N)
  ==. (shiftStringRight target x input lo) `C` (map (shiftStringRight target x input) N)
  ==. (stringLen x + lo) `C` N
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? isGoodIndexConcatFront input x target lo  -- ( => IsGoodIndex (concatString x input) target (stringLen x + lo))
  *** QED 
  | lo == hi
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) N
  ==. N
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 

shiftIndexesRight' lo hi x input target
  | isGoodIndex input target lo
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (lo `C` makeIndices input target (lo+1) hi)
  ==. (shiftStringRight target x input lo) `C` (map (shiftStringRight target x input) (makeIndices input target (lo+1) hi))
  ==. (shift (stringLen x) lo) `C` (makeIndices (concatString x input) target (stringLen x + (lo+1)) (stringLen x + hi))
      ? shiftIndexesRight' (lo+1) hi x input target
  ==. (stringLen x + lo) `C` (makeIndices (concatString x input) target (stringLen x + (lo+1)) (stringLen x + hi))
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 
  | otherwise
  =   map (shiftStringRight target x input) (makeIndices input target lo hi)
  ==. map (shiftStringRight target x input) (makeIndices input target (lo + 1) hi)
  ==. makeIndices (concatString x input) target (stringLen x + (lo+1)) (stringLen x + hi)
      ? shiftIndexesRight' (lo+1) hi x input target
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 


{-@ shiftIndexesLeft
  :: xi:SMTString 
  -> yi:SMTString 
  -> zi:SMTString 
  -> tg:{SMTString | stringLen tg <= stringLen yi } 
  -> {  makeNewIndices xi (concatString yi zi) tg == castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)}
  @-}
shiftIndexesLeft :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexesLeft xi yi zi tg
  | stringLen tg < 2 
  =   makeNewIndices xi (concatString yi zi) tg 
  ==. N
  ==. makeNewIndices xi yi tg 
  ==. castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
  *** QED 
  | otherwise
  =   makeNewIndices xi (concatString yi zi) tg 
  ==. makeIndices (concatString xi (concatString yi zi)) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
  ==. makeIndices (concatString (concatString xi yi) zi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
     ?concatStringAssoc xi yi zi 
  ==. makeIndices (concatString xi yi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)                
      ? concatmakeNewIndices (maxInt (stringLen xi - (stringLen tg-1)) 0) (stringLen xi - 1) tg (concatString xi yi) zi 
  ==. makeNewIndices xi yi tg 
  ==. castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)
  *** QED 

{-@ concatmakeNewIndices
  :: lo:Nat -> hi:Int
  -> target: SMTString
  -> input : {SMTString | hi + stringLen target <= stringLen input } 
  -> input': SMTString   
  -> {  makeIndices (concatString input input') target lo hi == makeIndices input target lo hi }
  / [hi - lo]  @-}
concatmakeNewIndices :: Int -> Int -> SMTString -> SMTString -> SMTString  -> Proof
concatmakeNewIndices lo hi target input input'
  | hi < lo 
  =   makeIndices input target lo hi
  ==. N
  ==. makeIndices (concatString input input') target lo hi 
  *** QED 
  | lo == hi, isGoodIndex input target lo
  =   makeIndices input target lo hi
  ==. lo `C` N
  ==. makeIndices (concatString input input') target lo hi 
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
  | lo == hi
  =  makeIndices input target lo hi 
  ==. N
  ==. makeIndices (concatString input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
concatmakeNewIndices lo hi target input input' 
  | isGoodIndex input target lo
  =   makeIndices input target lo hi
  ==. lo `C` (makeIndices input target (lo + 1) hi)
  ==. lo `C` (makeIndices (concatString input input') target (lo + 1) hi)
       ? concatmakeNewIndices (lo+1) hi target input input'
  ==. makeIndices  (concatString input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
  | otherwise 
  =   makeIndices input target lo hi
  ==. makeIndices input target (lo + 1) hi
  ==. makeIndices (concatString input input') target (lo + 1) hi
       ? concatmakeNewIndices (lo+1) hi target input input'
  ==. makeIndices  (concatString input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 



{-@ isGoodIndexConcatFront 
  :: input:SMTString -> input':SMTString -> tg:SMTString -> i:Nat
  -> {((isGoodIndex input tg i) <=> isGoodIndex (concatString input' input) tg (stringLen input' + i) )
     } @-}
isGoodIndexConcatFront :: SMTString -> SMTString -> SMTString -> Int -> Proof 
isGoodIndexConcatFront input input' tg i 
  =   isGoodIndex input tg i 
  ==. (subString input i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen input 
      && 0 <= i)  
  ==. (subString input i (stringLen tg)  == tg  
      && (stringLen input' + i) + stringLen tg <= stringLen (concatString input' input) 
      && 0 <= i)  
  ==. (subString (concatString input' input) (stringLen input' + i) (stringLen tg)  == tg  
      && (stringLen input' + i) + stringLen tg <= stringLen (concatString input' input) 
      && 0 <= (stringLen input' + i))  
      ? (subStringConcatFront input input' (stringLen tg) i *** QED)
  ==. isGoodIndex (concatString input' input) tg (stringLen input' + i) 
  *** QED 


{-@ isGoodIndexConcatString 
  :: input:SMTString -> input':SMTString -> tg:SMTString -> i:{Int | i + stringLen tg <= stringLen input }
  -> {((isGoodIndex input tg i) <=> isGoodIndex (concatString input input') tg i)
     } @-}
isGoodIndexConcatString :: SMTString -> SMTString -> SMTString -> Int -> Proof 
isGoodIndexConcatString input input' tg i 
  =   isGoodIndex input tg i 
  ==. (subString input i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen input
      && 0 <= i) 
  ==. (subString (concatString input input') i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen input 
      && 0 <= i)   
      ? (subStringConcatBack input input' (stringLen tg) i *** QED )
  ==. (subString (concatString input input') i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen (concatString input input') 
      && 0 <= i)   
      ? (((stringLen input <= stringLen (concatString input input') *** QED ) &&& (concatLen input input') *** QED))
  ==. isGoodIndex (concatString input input') tg i 
  *** QED 


mapShiftZero :: SMTString -> SMTString -> List Int -> Proof
{-@ mapShiftZero :: target:SMTString -> i:SMTString -> is:List (GoodIndex i target) 
  -> {map (shiftStringRight target stringEmp i) is == is } 
  / [llen is] @-}
mapShiftZero target i N
  =   map (shiftStringRight target stringEmp i) N ==. N *** QED  
mapShiftZero target i (C x xs)
  =   map (shiftStringRight target stringEmp i) (C x xs) 
  ==. shiftStringRight target stringEmp i x `C` map (shiftStringRight target stringEmp i) xs
  ==. shift (stringLen stringEmp) x `C` map (shiftStringRight target stringEmp i) xs
  ==. shift 0 x `C` map (shiftStringRight target stringEmp i) xs
  ==. x `C` map (shiftStringRight target stringEmp i) xs
  ==. x `C` xs ? mapShiftZero target i xs 
  *** QED 


{-@ mapShiftIndex :: tg:SMTString -> xi:SMTString -> yi:SMTString -> zi:SMTString -> xs:List (GoodIndex yi tg)
  -> {map (shiftStringRight tg xi yi) xs == map (shiftStringRight tg xi (concatString yi zi)) xs} / [llen xs] @-}
mapShiftIndex :: SMTString -> SMTString -> SMTString -> SMTString -> List Int -> Proof
mapShiftIndex tg xi yi zi N 
  = map (shiftStringRight tg xi yi) N ==. N ==. map (shiftStringRight tg xi (concatString yi zi)) N *** QED 
  *** QED 
mapShiftIndex tg xi yi zi zs@(C i0 is0)
  =   let is = castGoodIndexRightList tg yi zi is0 
          i  = castGoodIndexRight     tg yi zi i0  in 
      map (shiftStringRight tg xi yi) (C i is) 
  ==. C (shiftStringRight tg xi yi i) (map (shiftStringRight tg xi yi) is)
  ==. C (shift (stringLen xi) i) (map (shiftStringRight tg xi yi) is)
  ==. C (shiftStringRight tg xi (concatString yi zi) i) (map (shiftStringRight tg xi yi) is)
  ==. C (shiftStringRight tg xi (concatString yi zi) i) (map (shiftStringRight tg xi (concatString yi zi)) is)
       ? mapShiftIndex tg xi yi zi is
  ==. map (shiftStringRight tg xi (concatString yi zi)) (C i is)
  *** QED 



{-@ shiftNewIndices
  :: xi:SMTString 
  -> yi:SMTString 
  -> zi:SMTString 
  -> tg:{SMTString | stringLen yi < stringLen tg  } 
  -> {  append (makeNewIndices xi (concatString yi zi) tg) (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)) == append (castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)) (makeNewIndices (concatString xi yi) zi tg)
     }
  @-}
shiftNewIndices :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftNewIndices xi yi zi tg 
  | stringLen tg < 2 
  =   append (makeNewIndices xi (concatString yi zi) tg) (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)) 
  ==. append N (map (shiftStringRight tg xi (concatString yi zi)) N) 
  ==. map (shiftStringRight tg xi (concatString yi zi)) N 
  ==. N 
  ==. append N N
  ==. append (makeNewIndices xi yi tg) (makeNewIndices (concatString xi yi) zi tg)
  ==. append (castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)) (makeNewIndices (concatString xi yi) zi tg)
  *** QED 

shiftNewIndices xi yi zi tg 
  | stringLen xi == 0 
  =   append (makeNewIndices xi (concatString yi zi) tg) 
                  (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg))
  ==. append (makeNewIndices stringEmp (concatString yi zi) tg) 
                  (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg))
  ? stringEmpProp xi 
  ==. append (makeNewIndices stringEmp (concatString yi zi) tg) 
                  (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg))
  ? makeNewIndicesNullRight (concatString yi zi) tg
  ==. append N
                  (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg))
  ==. map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)
       ? stringEmpProp xi
  ==. map (shiftStringRight tg stringEmp (concatString yi zi)) (makeNewIndices yi zi tg)
      ? mapShiftZero tg (concatString yi zi) (makeNewIndices yi zi tg)
  ==. makeNewIndices yi zi tg
  ==. makeNewIndices (concatString xi yi) zi tg
        ? concatEmpLeft xi yi 
  ==. append N (makeNewIndices (concatString xi yi) zi tg)
  ==. append (makeNewIndices stringEmp yi tg) (makeNewIndices (concatString xi yi) zi tg)
       ? makeNewIndicesNullRight yi tg
  ==. append (makeNewIndices xi yi tg) (makeNewIndices (concatString xi yi) zi tg)
      ? stringEmpProp xi
  ==. append (castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)) (makeNewIndices (concatString xi yi) zi tg)
  *** QED 
  | stringLen yi == 0 
  =   append (makeNewIndices xi (concatString yi zi) tg) 
                  (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg))
  ==. append (makeNewIndices xi zi tg) 
                  (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg))
      ? (stringEmpProp yi &&& concatEmpLeft yi zi)
  ==. append (makeNewIndices xi zi tg) 
                  (map (shiftStringRight tg xi zi) (makeNewIndices stringEmp zi tg))
  ==. append (makeNewIndices xi zi tg) 
                  (map (shiftStringRight tg xi (concatString stringEmp zi)) N)
      ? makeNewIndicesNullRight zi tg 
  ==. append (makeNewIndices xi zi tg) 
                  N
  ==. makeNewIndices xi zi tg 
       ? appendNil (makeNewIndices xi zi tg)
  ==. makeNewIndices (concatString xi yi) zi tg
       ? concatEmpRight xi yi
  ==. append N (makeNewIndices (concatString xi yi) zi tg)
  ==. append (makeNewIndices xi stringEmp tg) (makeNewIndices (concatString xi yi) zi tg)
       ? makeNewIndicesNullLeft xi tg 
  ==. append (makeNewIndices xi yi tg) (makeNewIndices (concatString xi yi) zi tg)
  ==. append (castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)) (makeNewIndices (concatString xi yi) zi tg)
       ? stringEmpProp yi
  *** QED 
  | stringLen yi - stringLen tg == -1 
  = let minidx = maxInt (stringLen xi - stringLen tg + 1) 0 in 
      append (makeNewIndices xi (concatString yi zi) tg) 
                  (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi (concatString yi zi)) 
                            (makeIndices (concatString yi zi) tg
                                          (maxInt (stringLen yi - stringLen tg +1) 0)
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi (concatString yi zi)) 
                            (makeIndices (concatString yi zi) tg
                                          (maxInt 0 0)
                                          (stringLen yi -1)
                            ))  
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi (concatString yi zi)) 
                            (makeIndices (concatString yi zi) tg
                                          0
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndices (concatString xi (concatString yi zi)) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? shiftIndexesRight' 0 (stringLen yi -1) xi (concatString yi zi) tg 
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? concatStringAssoc xi yi zi 

  ==. append (append 

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi)
                                (stringLen xi -1))

                                ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) 
      ? mergeIndices (concatString (concatString xi yi) zi) tg 
                     minidx -- maxInt (stringLen xi - stringLen tg + 1) 0
                     (stringLen xi -1)
                     (stringLen xi -1)
  ==. append (append 

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  N

                                ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) 
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) 
      ? appendNil (makeIndices (concatString (concatString xi yi) zi) tg
                                    minidx
                                    (stringLen xi + stringLen yi - stringLen tg))
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi -1))

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                ((stringLen xi))
                                (stringLen xi + stringLen yi -1))
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx 
                                (stringLen (concatString xi yi)  - stringLen tg))

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1))

  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi)
                                (stringLen xi + stringLen yi  - 1)
                  )
      ? catIndices (concatString xi yi) zi tg minidx (stringLen xi-1)
  ==. append (makeIndices (concatString xi yi) tg 
                                minidx 
                                -- maxInt (stringLen xi - stringLen tg + 1) 0 && 2 <= stringLen tg
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi)
                                (stringLen xi + stringLen yi  - 1)
                  )

  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen xi) 0)
                                (stringLen xi + stringLen yi  - 1)
                  )


  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen xi + stringLen yi - stringLen tg + 1) 0)
                                (stringLen xi + stringLen yi  - 1)
                  )

  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen (concatString xi yi) - stringLen tg + 1) 0)
                                (stringLen (concatString xi yi) - 1)
                  )
  ==. append (makeIndices (concatString xi yi) tg 
                                (maxInt (stringLen xi - stringLen tg +1) 0)
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen (concatString xi yi) - stringLen tg + 1) 0)
                                (stringLen (concatString xi yi) - 1)
                  )
  ==. append (makeNewIndices xi yi tg) (makeNewIndices (concatString xi yi) zi tg)
  ==. append (castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)) (makeNewIndices (concatString xi yi) zi tg)
  *** QED 
shiftNewIndices xi yi zi tg 
-- THIS ALWAYS HOLDS 
--   | stringLen yi + 1 <= stringLen tg
  | 0 <= stringLen xi + stringLen yi - stringLen tg
 --  , 0 < stringLen xi 
  = let minidx = maxInt (stringLen xi - stringLen tg + 1) 0 in 
      append (makeNewIndices xi (concatString yi zi) tg) 
                  (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi (concatString yi zi)) 
                            (makeIndices (concatString yi zi) tg
                                          (maxInt (stringLen yi - stringLen tg +1) 0)
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                minidx
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi (concatString yi zi)) 
                            (makeIndices (concatString yi zi) tg
                                           0
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndices (concatString xi (concatString yi zi)) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? shiftIndexesRight' 0 (stringLen yi -1) xi (concatString yi zi) tg 
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? concatStringAssoc xi yi zi 

  ==. append (append 

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg + 1)
                                (stringLen xi -1))

                                ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) 
      ? mergeIndices (concatString (concatString xi yi) zi) tg 
                     minidx -- maxInt (stringLen xi - stringLen tg + 1) 0
                     (stringLen xi + stringLen yi - stringLen tg)
                     (stringLen xi -1)
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx 
                                (stringLen xi + stringLen yi - stringLen tg))

                 (append

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg +1)
                                (stringLen xi -1))

                                
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) )
      ? appendAssoc
              (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))
              (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg+1)
                                (stringLen xi -1))
              (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1))

  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                ((stringLen xi + stringLen yi - stringLen tg+1))
                                (stringLen xi + stringLen yi -1))
     ? mergeIndices (concatString (concatString xi yi) zi) tg 
                  ((stringLen xi + stringLen yi - stringLen tg+1))
                  (stringLen xi-1)
                  (stringLen xi + stringLen yi -1)

  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx 
                                (stringLen (concatString xi yi)  - stringLen tg))

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg + 1)
                                (stringLen xi + stringLen yi -1))

  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg + 1)
                                (stringLen xi + stringLen yi  - 1)
                  )
      ? catIndices (concatString xi yi) zi tg minidx (stringLen xi-1)

  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen xi + stringLen yi - stringLen tg + 1) 0)
                                (stringLen xi + stringLen yi  - 1)
                  )

  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen (concatString xi yi) - stringLen tg + 1) 0)
                                (stringLen (concatString xi yi) - 1)
                  )
  ==. append (makeIndices (concatString xi yi) tg 
                                (maxInt (stringLen xi - stringLen tg +1) 0)
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen (concatString xi yi) - stringLen tg + 1) 0)
                                (stringLen (concatString xi yi) - 1)
                  )
  ==. append (makeNewIndices xi yi tg) (makeNewIndices (concatString xi yi) zi tg)
  ==. append (castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)) (makeNewIndices (concatString xi yi) zi tg)
  *** QED 

--   | stringLen yi + 1 <= stringLen tg
  | stringLen xi + stringLen yi < stringLen tg
  =   append (makeNewIndices xi (concatString yi zi) tg) 
                  (map (shiftStringRight tg xi (concatString yi zi)) (makeNewIndices yi zi tg)) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi (concatString yi zi)) 
                            (makeIndices (concatString yi zi) tg
                                          (maxInt (stringLen yi - stringLen tg +1) 0)
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                0
                                (stringLen xi -1)) 
                  (map (shiftStringRight tg xi (concatString yi zi)) 
                            (makeIndices (concatString yi zi) tg
                                           0
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                0
                                (stringLen xi -1)) 
                  (makeIndices (concatString xi (concatString yi zi)) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? shiftIndexesRight' 0 (stringLen yi -1) xi (concatString yi zi) tg 
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                0
                                (stringLen xi -1)) 
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? concatStringAssoc xi yi zi 

  ==. makeIndices (concatString (concatString xi yi) zi) tg
                                0
                                (stringLen (concatString xi yi) - 1)
      ? mergeIndices (concatString (concatString xi yi) zi) tg 
                    0 
                    (stringLen xi-1) 
                    (stringLen (concatString xi yi) -1)

  ==. append N    (makeIndices (concatString (concatString xi yi) zi) tg
                                0
                                (stringLen (concatString xi yi) - 1)
                  )

  ==. append (makeIndices (concatString xi yi) tg 
                                0
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                0
                                (stringLen (concatString xi yi) - 1)
                  )
      ? smallInput (concatString xi yi) tg 0 (stringLen xi -1)
  ==. append (makeIndices (concatString xi yi) tg 
                                (maxInt (stringLen xi - stringLen tg +1) 0)
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen (concatString xi yi) - stringLen tg + 1) 0)
                                (stringLen (concatString xi yi) - 1)
                  )
  ==. append (makeNewIndices xi yi tg) (makeNewIndices (concatString xi yi) zi tg)
  ==. append (castGoodIndexRightList tg (concatString xi yi) zi (makeNewIndices xi yi tg)) (makeNewIndices (concatString xi yi) zi tg)
  *** QED 


smallInput :: SMTString -> SMTString -> Int -> Int -> Proof  
{-@ smallInput :: input:SMTString -> target:{SMTString | stringLen input < stringLen target } -> lo:Nat -> hi:Int 
           -> {makeIndices input target lo hi == N } 
           / [hi -lo]
  @-}
smallInput input target lo hi 
  | hi < lo 
  = makeIndices input target lo hi 
  ==. N
  *** QED  
  | lo == hi, not (isGoodIndex input target lo)
  = makeIndices input target lo hi 
  ==. N
  *** QED  
  | not (isGoodIndex input target lo)
  = makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. N ? smallInput input target (lo+1) hi 
  *** QED  

maxIndices :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ maxIndices 
  :: input:SMTString -> target:SMTString -> lo:{Nat | stringLen input < lo + stringLen target} -> hi:Int
  -> {makeIndices input target lo hi = N}
  / [hi - lo ] @-}
maxIndices input target lo hi 
  | hi < lo 
  =   makeIndices input target lo hi  
  ==. N
  *** QED 
  | lo == hi, not (isGoodIndex input target lo)
  =   makeIndices input target lo hi  
  ==. N
  *** QED 
  | not (isGoodIndex input target lo)
  =   makeIndices input target lo hi
  ==. N 
  ==. makeIndices input target (lo+1) hi 
      ? maxIndices input target (lo+1) hi 
  *** QED 


mergeIndices :: SMTString -> SMTString -> Int -> Int -> Int -> Proof
{-@ mergeIndices 
  :: input:SMTString -> target:SMTString -> lo:Nat -> mid:{Int | lo <= mid} -> hi:{Int | mid <= hi} 
  -> {makeIndices input target lo hi == append (makeIndices input target lo mid) (makeIndices input target (mid+1) hi)} 
  / [mid] @-}
mergeIndices input target lo mid hi 
  | lo == mid, isGoodIndex input target lo 
  =   append (makeIndices input target lo mid) (makeIndices input target (mid+1) hi)
  ==. append (makeIndices input target lo lo)  (makeIndices input target (mid+1) hi)
  ==. append (lo `C` N)  (makeIndices input target (mid+1) hi)
  ==. lo  `C` (append N  (makeIndices input target (lo+1) hi))
  ==. lo  `C` (makeIndices input target (lo+1) hi)
  ==. makeIndices input target lo hi
  *** QED 
  | lo == mid, not (isGoodIndex input target lo)
  =   append (makeIndices input target lo mid) (makeIndices input target (mid+1) hi)
  ==. append (makeIndices input target lo lo)  (makeIndices input target (mid+1) hi)
  ==. append (lo `C` N)  (makeIndices input target (mid+1) hi)
  ==. (append N  (makeIndices input target (lo+1) hi))
  ==. makeIndices input target lo hi
  *** QED 
  | lo < mid, not (isGoodIndex input target mid)
  =   makeIndices input target lo hi
  ==. append (makeIndices input target lo (mid-1)) 
                  (makeIndices input target mid hi)
       ? mergeIndices input target lo (mid-1) hi 

  ==. append (makeIndices input target lo (mid-1)) 
                  (makeIndices input target (mid+1) hi)

  ==. append (makeIndices input target lo mid) 
                  (makeIndices input target (mid+1) hi)
      ?makeNewIndicesBadLast input target lo mid
  *** QED 
  | lo < mid, isGoodIndex input target mid
  =   makeIndices input target lo hi
  ==. append (makeIndices input target lo (mid-1)) 
                  (makeIndices input target mid hi)
       ? mergeIndices input target lo (mid-1) hi 

  ==. append (makeIndices input target lo (mid-1)) 
                  (mid `C` makeIndices input target (mid+1) hi)


  ==. append (makeIndices input target lo (mid-1)) 
                  (mid `C` (append N (makeIndices input target (mid+1) hi)))

  ==. append (makeIndices input target lo (mid-1)) 
                  (append (C mid N) (makeIndices input target (mid+1) hi))

  ==. append (append (makeIndices input target lo (mid-1)) (C mid N)) 
                  (makeIndices input target (mid+1) hi)
      ? appendAssoc (makeIndices input target lo (mid-1)) (C mid N) (makeIndices input target (mid+1) hi)

  ==. append (makeIndices input target lo mid) 
                  (makeIndices input target (mid+1) hi)
      ?makeNewIndicesGoodLast input target lo mid
  *** QED 


makeNewIndicesGoodLast, makeNewIndicesBadLast 
  :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ makeNewIndicesGoodLast 
  :: input:SMTString -> target:SMTString -> lo:Nat -> hi:{Int | lo <= hi && (isGoodIndex input target hi)}
  -> {makeIndices input target lo hi == append (makeIndices input target lo (hi-1)) (C hi N)}
  / [hi - lo] @-}
makeNewIndicesGoodLast input target lo hi 
  | lo == hi, (isGoodIndex input target lo)
  =   makeIndices input target lo hi 
  ==. hi `C` N 
  ==. append (N) (C hi N)
  ==. append (makeIndices input target lo (hi-1)) (C hi N)
  *** QED 
  | not (isGoodIndex input target lo), isGoodIndex input target hi 
  =   makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. append (makeIndices input target (lo+1) (hi-1)) (C hi N)
       ? makeNewIndicesGoodLast input target (lo+1) hi  
  ==. append (makeIndices input target lo (hi-1)) (C hi N)
  *** QED 
  | isGoodIndex input target lo, isGoodIndex input target hi
  =   makeIndices input target lo hi 
  ==. lo `C` makeIndices input target (lo+1) hi
  ==. lo `C` (append (makeIndices input target (lo+1) (hi-1)) (C hi N))
       ? makeNewIndicesGoodLast input target (lo+1) hi  
  ==. (append (lo `C` makeIndices input target (lo+1) (hi-1)) (C hi N))
  ==. append (makeIndices input target lo (hi-1)) (C hi N)
  *** QED 

{-@ makeNewIndicesBadLast 
  :: input:SMTString -> target:SMTString -> lo:Nat -> hi:{Int | lo <= hi && (not (isGoodIndex input target hi))}
  -> {makeIndices input target lo hi == makeIndices input target lo (hi-1)}
  / [hi - lo]
@-}
-- NV sweet proof 
makeNewIndicesBadLast input target lo hi 
  | lo == hi, not (isGoodIndex input target lo)
  =   makeIndices input target lo (hi-1) 
  ==. N 
  ==. makeIndices input target lo hi
  *** QED 
  | not (isGoodIndex input target lo), not (isGoodIndex input target hi) 
  =   makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. makeIndices input target (lo+1) (hi-1)
       ? makeNewIndicesBadLast input target (lo+1) hi   
  ==. makeIndices input target lo (hi-1)
  *** QED 
  | isGoodIndex input target lo , not (isGoodIndex input target hi) 
  =   makeIndices input target lo hi 
  ==. lo `C` makeIndices input target (lo+1) hi
  ==. lo `C` makeIndices input target (lo+1) (hi-1)
       ? makeNewIndicesBadLast input target (lo+1) hi   
  ==. makeIndices input target lo (hi-1)
  *** QED 


catIndices :: SMTString -> SMTString -> SMTString -> Int -> Int -> Proof 
{-@ catIndices 
     :: input:SMTString -> x:SMTString 
     -> target:{SMTString | 0 <= stringLen input - stringLen target + 1} 
     -> lo:{Nat | lo <= stringLen input - stringLen target } 
     -> hi:{Int | stringLen input - stringLen target <= hi}
     -> { makeIndices input target lo hi == makeIndices (concatString input x) target lo (stringLen input - stringLen target) }
  @-}
catIndices input x target lo hi 
  =   makeIndices input target lo hi
  ==. append (makeIndices input target lo (stringLen input - stringLen target))
                  (makeIndices input target (stringLen input - stringLen target + 1) hi)
       ? mergeIndices input target lo (stringLen input - stringLen target) hi
  ==. append (makeIndices input target lo (stringLen input - stringLen target))
                  N
       ? maxIndices input target (stringLen input - stringLen target + 1) hi
  ==. makeIndices input target lo (stringLen input - stringLen target)
       ? appendNil (makeIndices input target lo (stringLen input - stringLen target))
  ==. makeIndices (concatString input x) target lo (stringLen input - stringLen target)
       ? concatmakeNewIndices lo (stringLen input - stringLen target) target input x 
  *** QED 

