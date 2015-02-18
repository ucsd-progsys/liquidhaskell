{-# LANGUAGE FlexibleContexts           #-} 
{-# LANGUAGE FlexibleInstances          #-}


module Language.Fixpoint.PrettyPrint where

import Text.PrettyPrint.HughesPJ
import Language.Fixpoint.Types
import Language.Fixpoint.Misc
import Control.Applicative      ((<$>))
import Text.Parsec
import qualified Data.Text as T

class PPrint a where
  pprint :: a -> Doc

showpp :: (PPrint a) => a -> String 
showpp = render . pprint 

instance PPrint a => PPrint (Maybe a) where
  pprint = maybe (text "Nothing") ((text "Just" <+>) . pprint)

instance PPrint a => PPrint [a] where
  pprint = brackets . intersperse comma . map pprint

instance (PPrint a, PPrint b, PPrint c) => PPrint (a, b, c) where
  pprint (x, y, z)  = parens $ (pprint x) <> text "," <> (pprint y) <> text "," <> (pprint z) 


instance (PPrint a, PPrint b) => PPrint (a,b) where
  pprint (x, y)  = (pprint x) <+> text ":" <+> (pprint y)

instance PPrint SourcePos where
  pprint = text . show 

instance PPrint () where
  pprint = text . show 

instance PPrint String where 
  pprint = text 

instance PPrint Int where
  pprint = toFix

instance PPrint Integer where
  pprint = toFix

instance PPrint Constant where
  pprint = toFix

instance PPrint Brel where
  pprint Eq = text "=="
  pprint Ne = text "/="
  pprint r  = toFix r

instance PPrint Bop where
  pprint  = toFix 

instance PPrint Sort where
  pprint = toFix  

instance PPrint Symbol where
  pprint = toFix

instance PPrint SymConst where
  pprint (SL x)          = doubleQuotes $ text $ T.unpack x

instance PPrint Expr where
  pprint (EApp f es)     = parens $ intersperse empty $ (pprint f) : (pprint <$> es) 
  pprint (ESym c)        = pprint c 
  pprint (ECon c)        = pprint c 
  pprint (EVar s)        = pprint s
  pprint (ELit s _)      = pprint s
  pprint (ENeg e)        = parens $ text "-" <+> parens (pprint e)
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
  pprint (PAnd ps)       = parens $ pprintBin trueD  andD ps
  pprint (POr  ps)       = parens $ pprintBin falseD orD  ps 
  pprint (PAtom r e1 e2) = parens $ pprint e1 <+> pprint r <+> pprint e2
  pprint (PAll xts p)    = text "forall" <+> toFix xts <+> text "." <+> pprint p

trueD  = text "true"
falseD = text "false"
andD   = text "&&"
orD    = text "||"

pprintBin b _ [] = b
pprintBin _ o xs = intersperse o $ pprint <$> xs 

instance PPrint Refa where
  pprint (RConc p)     = pprint p
  pprint k             = toFix k
 
instance PPrint Reft where 
  pprint r@(Reft (_,ras)) 
    | isTauto r        = text "true"
    | otherwise        = {- intersperse comma -} pprintBin trueD andD $ flattenRefas ras

 

instance PPrint SortedReft where
  pprint (RR so (Reft (v, ras))) 
    = braces 
    $ (pprint v) <+> (text ":") <+> (toFix so) <+> (text "|") <+> pprint ras

instance PPrint a => PPrint (Located a) where
  pprint (Loc _ x) = pprint x







