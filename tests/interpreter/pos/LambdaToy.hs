{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--interpreter" @-}

module LambdaToy where

{-@ reflect isPred @-}
{-@ isPred :: e:Expr -> { b:Bool | (isTerm e => b) } @-}
isPred :: Expr -> Bool --     (outside of refinements of course)
isPred (Bc _)           = True
isPred (App e e')       = isTerm e && isTerm e'




data Expr = Bc Bool                   -- True, False
          | App Expr Expr             -- e e'          applications
{-@ type Term = { e:Expr | isTerm e } @-}

{-@ reflect isTerm @-} -- a legal program term is an expression that does not contain Conj
{-@ isTerm :: e:Expr -> { b:Bool | b => isPred e } @-}
isTerm :: Expr -> Bool --     (outside of refinements of course)
isTerm (Bc _)           = True
isTerm (App e e')       = isTerm e && isTerm e'

