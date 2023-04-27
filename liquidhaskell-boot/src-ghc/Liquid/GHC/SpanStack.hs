{-# LANGUAGE BangPatterns #-}

module Liquid.GHC.SpanStack
   ( -- * Stack of positions
     Span (..)
   , SpanStack

     -- * Creating Stacks
   , empty, push

     -- * Using Stacks
   , srcSpan

     -- * Creating general spans
   , showSpan
   ) where

import           Prelude                   hiding (error)
import           Data.Maybe                       (listToMaybe, fromMaybe)
import           Liquid.GHC.Misc (tickSrcSpan, showPpr)
import qualified Liquid.GHC.API  as Ghc
import           Liquid.GHC.API  ( SrcSpan
                                                  , fsLit
                                                  , getSrcSpan
                                                  , isGoodSrcSpan
                                                  , mkGeneralSrcSpan
                                                  )

-- | Opaque type for a stack of spans
newtype SpanStack = SpanStack { unStack :: [(Span, SrcSpan)] }

--------------------------------------------------------------------------------
empty :: SpanStack
--------------------------------------------------------------------------------
empty = SpanStack []

--------------------------------------------------------------------------------
push :: Span -> SpanStack -> SpanStack
--------------------------------------------------------------------------------
push !s stk -- @(SpanStack stk)
  | Just sp <- spanSrcSpan s = SpanStack ((s, sp) : unStack stk)
  | otherwise                = stk

-- | A single span
data Span
  = Var  !Ghc.Var         -- ^ binder for whom we are generating constraint
  | Tick !Ghc.CoreTickish -- ^ nearest known Source Span
  | Span SrcSpan

instance Show Span where
  show (Var x)   = show x
  show (Tick tt) = showPpr tt
  show (Span s)  = show s 

--------------------------------------------------------------------------------
srcSpan :: SpanStack -> SrcSpan
--------------------------------------------------------------------------------
srcSpan s  = fromMaybe noSpan (mbSrcSpan s)
  where
    noSpan = showSpan "Yikes! No source information"

mbSrcSpan :: SpanStack -> Maybe SrcSpan
mbSrcSpan = fmap snd . listToMaybe  . unStack

spanSrcSpan :: Span -> Maybe SrcSpan
spanSrcSpan      = maybeSpan Nothing . go
  where
    go (Var x)   = getSrcSpan x
    go (Tick tt) = tickSrcSpan tt
    go (Span s)  = s 

maybeSpan :: Maybe SrcSpan -> SrcSpan -> Maybe SrcSpan
maybeSpan d sp
  | isGoodSrcSpan sp = Just sp
  | otherwise        = d

--------------------------------------------------------------------------------
showSpan :: (Show a) => a -> SrcSpan
--------------------------------------------------------------------------------
showSpan = mkGeneralSrcSpan . fsLit . show
