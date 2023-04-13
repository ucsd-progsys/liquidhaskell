{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--exact-data-cons" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!
{-@ infixr <~  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Imp where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import           Expressions -- hiding (And)

--------------------------------------------------------------------------------
-- | IMP Commands
--------------------------------------------------------------------------------
data Com 
  = Skip                      -- skip 
  | Assign Vname AExp         -- x := a
  | Seq    Com   Com          -- c1; c2
  | If     BExp  Com   Com    -- if b then c1 else c2
  | While  BExp  Com          -- while b c 
  deriving (Show)

{-@ reflect <~ @-}
(<~) :: Vname -> AExp -> Com 
x <~ a = Assign x a 

{-@ reflect @@ @-}
(@@) :: Com -> Com -> Com 
s1 @@ s2 = Seq s1 s2

