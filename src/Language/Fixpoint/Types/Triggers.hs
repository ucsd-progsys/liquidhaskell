{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}

module Language.Fixpoint.Types.Triggers (

    Triggered (..), Trigger(..),

    noTrigger, defaultTrigger,

    makeTriggers

    ) where

import qualified Data.Binary as B
import           Control.DeepSeq
import           GHC.Generics              (Generic)
import           Text.PrettyPrint.HughesPJ

import Language.Fixpoint.Types.Refinements
import Language.Fixpoint.Types.PrettyPrint 
import Language.Fixpoint.Misc              (errorstar)


data Triggered a = TR Trigger a
  deriving (Eq, Show, Functor, Generic)

data Trigger = NoTrigger | LeftHandSide
  deriving (Eq, Show, Generic)

instance PPrint Trigger where 
  pprintTidy _ = text . show 

instance PPrint a => PPrint (Triggered a) where 
  pprintTidy k (TR t x) = parens (pprintTidy k t <+> text ":" <+> pprintTidy k x)

noTrigger :: e -> Triggered e
noTrigger = TR NoTrigger

defaultTrigger :: e -> Triggered e
defaultTrigger = TR LeftHandSide

makeTriggers :: Triggered Expr -> [Expr]
makeTriggers (TR LeftHandSide e) = [getLeftHandSide e]
makeTriggers (TR NoTrigger    _) = errorstar "makeTriggers on NoTrigger"


getLeftHandSide :: Expr -> Expr
getLeftHandSide (ECst e _)
  = getLeftHandSide e
getLeftHandSide (PAll _ e)
  = getLeftHandSide e
getLeftHandSide (PExist _ e)
  = getLeftHandSide e
getLeftHandSide (PAtom eq lhs _)
  | eq == Eq || eq == Ueq
  = lhs
getLeftHandSide (PIff lhs _)
  = lhs
getLeftHandSide _
 = defaltPatter

-- NV TODO find out a valid, default pattern that does not instantiate the axiom
defaltPatter :: Expr
defaltPatter = PFalse

instance B.Binary Trigger
instance NFData   Trigger

instance (B.Binary a) => B.Binary (Triggered a)
instance (NFData a)   => NFData   (Triggered a)
