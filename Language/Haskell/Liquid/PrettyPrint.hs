-- | Module with all the printing routines

module Language.Haskell.Liquid.PrettyPrint (

  -- * Class for values that can be pretty printed 
  PPrint (..)
  
  ) where

import Text.PrettyPrint.HughesPJ
import Language.Fixpoint.Types
import Language.Haskell.Liquid.Types

-----------------------------------------------------------------------------

-- | Class for values that can be 
class PPrint a where
  pprint :: a -> Doc

pshow :: PPrint a => a -> String
pshow = render . pprint

-----------------------------------------------------------------------------

instance PPrint Integer where
  pprint = toFix

instance PPrint Constant where
  pprint = toFix i

instance PPrint Brel where
  toFix Eq = text "=="
  toFix Ne = text "/="
  pprint r = toFix r

instance PPrint Bop where
  pprint  = toFix 

instance PPrint Expr where
  pprint (EApp f es)     = parens $ intersperse empty $ pprint f : pprint es 
  pprint (ECon c)        = pprint c 
  pprint (EVar s)        = pprint s
  pprint (ELit s _)      = pprint s
  pprint (EBin o e1 e2)  = parens $ pprint e1 <+> pprint o <+> pprint e2
  pprint (EIte p e1 e2)  = parens $ text "if" <+> pprint p <+> text "then" <+> pprint e1 <+> text "else" <+> pprint e2 
  pprint (ECst e so)     = parens $ pprint e <+> text " : " <+> pprint so 
  pprint (EBot)          = text "_|_"

instance PPrint Pred where
  pprint PTop            = text "???"
  pprint PTrue           = trueD 
  pprint PFalse          = falseD
  pprint (PBexp e)       = parens $ pprint e
  pprint (PNot p)        = parens $ text "not" <+> parens (pprint p)
  pprint (PImp p1 p2)    = parens $ (pprint p1) <+> text "=>"  <+> (pprint p2)
  pprint (PIff p1 p2)    = parens $ (pprint p1) <+> text "<=>" <+> (pprint p2)
  pprint (PAnd ps)       = parens $ pprintBin trueD  (text "&&") ps
  pprint (POr  ps)       = parens $ pprintBin falseD (text "&&") ps 
  pprint (PAtom r e1 e2) = parens $ pprint e1 <+> pprint r <+> pprint e2
  pprint (PAll xts p)    = text "forall" <+> toFix xts <+> text "." <+> pprint p

trueD  = text "true"
falseD = text "false"

instance PPrint a => PPrint (Maybe a) where
  pprint = maybe (text "Nothing") ((text "Just" <+>) . pprint)

instance PPrint a => PPrint [a] where
  pprint = brackets . intersperse comma . map pprint

pprintBin b o []     = b
pprintBin b o [x]    = pprint x
pprintBin b o (x:xs) = pprint x <+> o <+> pprintBin b o xs 

instance PPrint SourcePos where
  pprint = toFix

instance PPrint Var where
  pprint = pprDoc 

instance PPrint Name where
  pprint = pprDoc 

instance PPrint Type where
  pprint = pprDoc

instance PPrint SourcePos where
  pprint = tshow 

instance PPrint a => PPrint (Located a) where
  pprint = pprint . val 



{- 
[hsenv]rjhala@ubuntu:~/research/liquid/liquidhaskell/Language (deepmeasure)$ ack-grep Fixpoint | grep "instance"

Haskell/Liquid/Constraint.hs:156:instance F.Fixpoint CGEnv where
Haskell/Liquid/Constraint.hs:213:instance F.Fixpoint SubC where
Haskell/Liquid/Constraint.hs:219:instance F.Fixpoint WfC where
Haskell/Liquid/Constraint.hs:222:instance F.Fixpoint Cinfo where
Haskell/Liquid/Constraint.hs:436:instance F.Fixpoint CGInfo where 
Haskell/Liquid/Constraint.hs:1196:instance F.Fixpoint REnv where

Haskell/Liquid/PredType.hs:52:instance F.Fixpoint TyConP where
Haskell/Liquid/PredType.hs:60:instance F.Fixpoint DataConP where

Haskell/Liquid/GhcInterface.hs:422:instance Fixpoint GhcSpec where
Haskell/Liquid/GhcInterface.hs:432:instance Fixpoint GhcInfo where 
Haskell/Liquid/GhcInterface.hs:449:instance Fixpoint TargetVars where

Haskell/Liquid/RefType.hs:108:instance Fixpoint Predicate where
Haskell/Liquid/RefType.hs:232:instance Fixpoint () where
Haskell/Liquid/RefType.hs:295:instance Fixpoint String where
Haskell/Liquid/RefType.hs:299:instance Fixpoint Class where
Haskell/Liquid/RefType.hs:303:instance (Eq p, Fixpoint p, TyConable c, Reftable r) => RefTypable p c String r where
Haskell/Liquid/RefType.hs:615:instance Fixpoint RTyVar where
Haskell/Liquid/RefType.hs:623:instance (Reftable s, Reftable  p, Fixpoint t) => Fixpoint (Ref t s (RType a b c p)) where
Haskell/Liquid/RefType.hs:633:instance (Reftable r) => Fixpoint (UReft r) where
Haskell/Liquid/RefType.hs:639:instance Fixpoint (UReft r) => Show (UReft r) where
Haskell/Liquid/RefType.hs:642:instance (Fixpoint a, Fixpoint b, Fixpoint c) => Fixpoint (a, b, c) where
Haskell/Liquid/RefType.hs:645:instance  Fixpoint t => Fixpoint (PVar t) where
Haskell/Liquid/RefType.hs:654:instance (RefTypable p c tv r) => Fixpoint (RType p c tv r) where
Haskell/Liquid/RefType.hs:657:instance Fixpoint (RType p c tv r) => Show (RType p c tv r) where
Haskell/Liquid/RefType.hs:660:instance Fixpoint RTyCon where
Haskell/Liquid/Annotate.hs:280:instance Fixpoint a => Fixpoint (AnnInfo a) where
Haskell/Liquid/Annotate.hs:292:instance Fixpoint Annot where
Haskell/Liquid/Measure.hs:161:instance Fixpoint Body where
Haskell/Liquid/Measure.hs:166:instance Fixpoint a => Fixpoint (BDataCon a) where
Haskell/Liquid/Measure.hs:171:instance Fixpoint a => Fixpoint (Def a) where
Haskell/Liquid/Measure.hs:176:instance (Fixpoint t, Fixpoint a) => Fixpoint (Measure t a) where
Haskell/Liquid/Measure.hs:181:instance (Fixpoint t, Fixpoint a) => Fixpoint (MSpec t a) where
Haskell/Liquid/Measure.hs:185:instance (Fixpoint t , Fixpoint a) => Show (Measure t a) where

-}
