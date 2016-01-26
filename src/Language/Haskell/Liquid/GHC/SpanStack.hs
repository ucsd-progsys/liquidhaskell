{-# LANGUAGE BangPatterns #-}

module Language.Haskell.Liquid.GHC.SpanStack
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
import           SrcLoc
import qualified Var
import           CoreSyn                   hiding (Tick, Var)
import           Name                             (getSrcSpan)
import           FastString                       (fsLit)
import           Data.Maybe                       (listToMaybe, fromMaybe)
import           Language.Haskell.Liquid.GHC.Misc (tickSrcSpan, showPpr)

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
  = Var  !Var.Var           -- ^ binder for whom we are generating constraint
  | Tick !(Tickish Var.Var) -- ^ nearest known Source Span

instance Show Span where
  show (Var x)   = show x
  show (Tick tt) = showPpr tt

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

maybeSpan :: Maybe SrcSpan -> SrcSpan -> Maybe SrcSpan
maybeSpan d sp
  | isGoodSrcSpan sp = Just sp
  | otherwise        = d

--------------------------------------------------------------------------------
showSpan :: (Show a) => a -> SrcSpan
--------------------------------------------------------------------------------
showSpan = mkGeneralSrcSpan . fsLit . show
