{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}


module Language.Fixpoint.PrettyPrint where

import           Control.Applicative       ((<$>))
import qualified Data.Text                 as T
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types
import           Text.Parsec
import           Text.PrettyPrint.HughesPJ
import qualified Data.HashMap.Strict as M

class PPrint a where
  pprint :: a -> Doc
  pprint = pprintPrec 0

  -- | Pretty-print something with a specific precedence.
  pprintPrec :: Int -> a -> Doc
  pprintPrec _ = pprint

showpp :: (PPrint a) => a -> String
showpp = render . pprint

instance PPrint a => PPrint (Maybe a) where
  pprint = maybe (text "Nothing") ((text "Just" <+>) . pprint)

instance PPrint a => PPrint [a] where
  pprint = brackets . intersperse comma . map pprint

instance (PPrint a, PPrint b) => PPrint (M.HashMap a b) where
  pprint = pprint . M.toList

instance (PPrint a, PPrint b, PPrint c) => PPrint (a, b, c) where
  pprint (x, y, z)  = parens $ pprint x <> text "," <> pprint y <> text "," <> pprint z


instance (PPrint a, PPrint b) => PPrint (a,b) where
  pprint (x, y)  = pprint x <+> text ":" <+> pprint y

instance PPrint SourcePos where
  pprint = text . show

instance PPrint Bool where
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
  pprint = text . symbolString

instance PPrint SymConst where
  pprint (SL x)          = doubleQuotes $ text $ T.unpack x


-- | Wrap the enclosed 'Doc' in parentheses only if the condition holds.
parensIf True  = parens
parensIf False = id

-- NOTE: The following Expr and Pred printers use pprintPrec to print
-- expressions with minimal parenthesization. The precedence rules are somewhat
-- fragile, and it would be nice to have them directly tied to the parser, but
-- the general idea is (from lowest to highest precedence):
--
-- 1 - if-then-else
-- 2 - => and <=>
-- 3 - && and ||
-- 4 - ==, !=, <, <=, >, >=
-- 5 - mod
-- 6 - + and -
-- 7 - * and /
-- 8 - function application
--
-- Each printer `p` checks whether the precedence of the context is greater than
-- its own precedence. If so, the printer wraps itself in parentheses. Then it
-- sets the contextual precedence for recursive printer invocations to
-- (prec p + 1).

opPrec Mod   = 5
opPrec Plus  = 6
opPrec Minus = 6
opPrec Times = 7
opPrec Div   = 7

instance PPrint Expr where
  pprintPrec _ (ESym c)        = pprint c
  pprintPrec _ (ECon c)        = pprint c
  pprintPrec _ (EVar s)        = pprint s
  pprintPrec _ (ELit s _)      = pprint s
  pprintPrec _ (EBot)          = text "_|_"
  pprintPrec z (ENeg e)        = parensIf (z > zn) $
                                   text "-" <> pprintPrec (zn+1) e
    where zn = 2
  pprintPrec z (EApp f es)     = parensIf (z > za) $
                                   intersperse empty $
                                     (pprint f) : (pprintPrec (za+1) <$> es)
    where za = 8
  pprintPrec z (EBin o e1 e2)  = parensIf (z > zo) $
                                   pprintPrec (zo+1) e1 <+>
                                   pprint o             <+>
                                   pprintPrec (zo+1) e2
    where zo = opPrec o
  pprintPrec z (EIte p e1 e2)  = parensIf (z > zi) $
                                   text "if"   <+> pprintPrec (zi+1) p  <+>
                                   text "then" <+> pprintPrec (zi+1) e1 <+>
                                   text "else" <+> pprintPrec (zi+1) e2
    where zi = 1
  pprintPrec _ (ECst e so)     = parens $ pprint e <+> text ":" <+> pprint so

instance PPrint Pred where
  pprintPrec _ PTop            = text "???"
  pprintPrec _ PTrue           = trueD
  pprintPrec _ PFalse          = falseD
  pprintPrec z (PBexp e)       = pprintPrec z e
  pprintPrec z (PNot p)        = parensIf (z > zn) $
                                   text "not" <+> pprintPrec (zn+1) p
    where zn = 8
  pprintPrec z (PImp p1 p2)    = parensIf (z > zi) $
                                   (pprintPrec (zi+1) p1) <+>
                                   text "=>"              <+>
                                   (pprintPrec (zi+1) p2)
    where zi = 2
  pprintPrec z (PIff p1 p2)    = parensIf (z > zi) $
                                   (pprintPrec (zi+1) p1) <+>
                                   text "<=>"             <+>
                                   (pprintPrec (zi+1) p2)
    where zi = 2
  pprintPrec z (PAnd ps)       = parensIf (z > za) $
                                   pprintBin (za+1) trueD  andD ps
    where za = 3
  pprintPrec z (POr  ps)       = parensIf (z > zo) $
                                   pprintBin (zo+1) falseD orD  ps
    where zo = 3
  pprintPrec z (PAtom r e1 e2) = parensIf (z > za) $
                                   pprintPrec (za+1) e1 <+>
                                   pprint r             <+>
                                   pprintPrec (za+1) e2
    where za = 4
  pprintPrec _ (PAll xts p)    = text "forall" <+> toFix xts <+> text "." <+> pprint p

trueD  = text "true"
falseD = text "false"
andD   = text " &&"
orD    = text " ||"

pprintBin _ b _ [] = b
pprintBin z _ o xs = intersperse o $ pprintPrec z <$> xs

instance PPrint Refa where
  pprintPrec z (Refa p)     = pprintPrec z p
  pprintPrec _ k            = toFix k

instance PPrint Reft where
  pprint r@(Reft (_,ra))
    | isTauto r        = text "true"
    | otherwise        = {- intersperse comma -} pprintBin z trueD andD flat
    where
      flat = flattenRefas [ra]
      z    = if length flat > 1 then 3 else 0

instance PPrint SortedReft where
  pprint (RR so (Reft (v, ras)))
    = braces
    $ (pprint v) <+> (text ":") <+> (toFix so) <+> (text "|") <+> pprint ras

instance PPrint a => PPrint (Located a) where
  pprint (Loc _ x) = pprint x
