{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE RankNTypes   #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module TypeFun where

{-@ predicate Btwn Lo N Hi = Lo <= N && N < Hi @-}

{-@ addUint8 :: x:_ -> y:{_ | Btwn 0 (x+y) 256} -> {v:_ | v = x + y} @-}
addUint8 :: Int -> Int -> Int
addUint8 = (+)

{-@ double :: Def (Arr (Cons {v:Int | Btwn 0 v 128} Nil) Int) @-}
double = proc body
  where 
    {-@ body :: {v:Int | Btwn 0 v 128} -> _ @-}
    body x = Body $ x `addUint8` x

type Arr = (:->)

type Cons = '(:)
type Nil = '[]

data Proc k = [k] :-> k

proc :: forall proc impl. IvoryProcDef proc impl => impl -> Def proc
proc x = Def

data Def (proc :: Proc *)
  = Def

data Body r = Body r

class IvoryProcDef (proc :: Proc *) impl | impl -> proc where

instance IvoryProcDef ('[] :-> a) (Body a) where

instance IvoryProcDef (args :-> ret) k
      => IvoryProcDef ((a ': args) :-> ret) (a -> k) where

