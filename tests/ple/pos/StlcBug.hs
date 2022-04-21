-- http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html 

{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

{-# LANGUAGE GADTs #-}

module StlcBug where

data Type 
  = TInt 
  | TBool 

data Op  
  = Add 
  | And 

data Val 
  = VBool Bool 
  | VInt  Int

data Result 
  = Result Val  
  | Stuck 

{-@ reflect isResTy @-}
isResTy :: Result -> Type -> Bool 
isResTy (Result v) t = isValTy v t 
isResTy Stuck      _ = False 

{-@ reflect isValTy @-}
isValTy :: Val -> Type -> Bool 
isValTy (VBool _) TBool = True 
isValTy (VInt _)  TInt  = True 
isValTy _         _     = False 

{-@ reflect opIn @-}
opIn :: Op -> Type 
opIn Add = TInt 
opIn And = TBool

{-@ foo :: o:Op -> v1:{Val | isValTy v1 (opIn o)} -> () @-}
foo :: Op -> Val -> () 
foo _ _ = () 

{-@ bar :: o:Op -> r:{Result | isResTy r (opIn o)} -> () @-}
bar :: Op -> Result -> ()
bar o (Result v) = foo o v 
bar o _          = () 

