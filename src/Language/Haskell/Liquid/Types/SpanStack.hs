{-# LANGUAGE BangPatterns #-}

module Language.Haskell.Liquid.Types.SpanStack
   ( -- * Stack of positions
     Span (..)
   , SpanStack

     -- * Creating Stacks
   , empty, push

     -- * Using Stacks
   , srcSpan

   ) where

import SrcLoc
import qualified Var
import CoreSyn                          hiding (Tick, Var)
import Name                             (getSrcSpan)
import FastString                       (fsLit)
import Language.Haskell.Liquid.GHC.Misc (tickSrcSpan, showPpr)
import Data.Maybe                       (fromMaybe)
import Language.Haskell.Liquid.Misc     (firstJust)

-- | Opaque type for a stack of spans
newtype SpanStack = SpanStack {unStack :: [Span]}

--------------------------------------------------------------------------------
empty :: SpanStack
--------------------------------------------------------------------------------
empty = SpanStack []

--------------------------------------------------------------------------------
push :: Span -> SpanStack -> SpanStack
--------------------------------------------------------------------------------
push !s (SpanStack stk) = SpanStack (s : stk)

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
srcSpan s = fromMaybe sp0 $ firstJust spanSrcSpan stk
  where
    stk   = unStack s
    sp0   = showSpan ("Span Stack:", stk)

spanSrcSpan :: Span -> Maybe SrcSpan
spanSrcSpan        = maybeSpan Nothing . go
  where
    go (Var x)   = getSrcSpan x
    go (Tick tt) = tickSrcSpan tt

maybeSpan :: Maybe SrcSpan -> SrcSpan -> Maybe SrcSpan
maybeSpan d sp
  | isGoodSrcSpan sp = Just sp
  | otherwise        = d

showSpan :: (Show a) => a -> SrcSpan
showSpan = mkGeneralSrcSpan . fsLit . show
