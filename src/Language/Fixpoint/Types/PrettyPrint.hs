{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}


module Language.Fixpoint.Types.PrettyPrint where

import           Debug.Trace               (trace)
import           Text.Parsec
import           Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.Boxes as B
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import           Language.Fixpoint.Utils.Misc

class Fixpoint a where
  toFix    :: a -> Doc
  simplify :: a -> a
  simplify =  id

showFix :: (Fixpoint a) => a -> String
showFix =  render . toFix


class PPrint a where
  pprint :: a -> Doc
  pprint = pprintPrec 0

  -- | Pretty-print something with a specific precedence.
  pprintPrec :: Int -> a -> Doc
  pprintPrec _ = pprint

showpp :: (PPrint a) => a -> String
showpp = render . pprint

tracepp :: (PPrint a) => String -> a -> a
tracepp s x = trace ("\nTrace: [" ++ s ++ "] : " ++ showpp x) x

instance PPrint Doc where
  pprint = id

instance PPrint a => PPrint (Maybe a) where
  pprint = maybe (text "Nothing") ((text "Just" <+>) . pprint)

instance PPrint a => PPrint [a] where
  pprint = brackets . intersperse comma . map pprint

instance PPrint a => PPrint (S.HashSet a) where
  pprint = pprint . S.toList

instance (PPrint a, PPrint b) => PPrint (M.HashMap a b) where
  pprint = pprintKVs . M.toList

pprintKVs :: (PPrint k, PPrint v) => [(k, v)] -> Doc
pprintKVs = vcat . punctuate (text "\n") . map pp1 -- . M.toList
  where
    pp1 (x,y) = pprint x <+> text ":=" <+> pprint y

instance (PPrint a, PPrint b, PPrint c) => PPrint (a, b, c) where
  pprint (x, y, z)  = parens $ pprint x <> text "," <> pprint y <> text "," <> pprint z


instance (PPrint a, PPrint b) => PPrint (a,b) where
  pprint (x, y)  = pprint x <+> text ":" <+> pprint y

instance PPrint Bool where
  pprint = text . show

instance PPrint Float where
  pprint = text . show

instance PPrint () where
  pprint = text . show

instance PPrint String where
  pprint = text

instance PPrint Int where
  pprint = tshow

instance PPrint Integer where
  pprint = integer

newtype DocTable = DocTable [(Doc, Doc)]

instance Monoid DocTable where
  mempty                              = DocTable []
  mappend (DocTable t1) (DocTable t2) = DocTable (t1 ++ t2)

class PTable a where
  ptable :: a -> DocTable

instance PPrint DocTable where
  pprint (DocTable kvs) = boxDoc $ B.hsep 1 B.left [ks', cs', vs']
    where
      (ks, vs)          = unzip kvs
      n                 = length kvs
      ks'               = B.vcat B.left  $ docBox <$> ks
      vs'               = B.vcat B.right $ docBox <$> vs
      cs'               = B.vcat B.left  $ replicate n $ B.text ":"

boxHSep :: Doc -> Doc -> Doc
boxHSep d1 d2 = boxDoc $ B.hcat B.top [docBox d1, docBox d2]

boxDoc :: B.Box -> Doc
boxDoc = text . B.render

docBox :: Doc -> B.Box
docBox = B.text . render
