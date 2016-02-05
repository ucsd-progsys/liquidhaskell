{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}

module Language.Fixpoint.Types.PrettyPrint where

import           Debug.Trace               (trace)
import           Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.Boxes as B
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import           Language.Fixpoint.Misc
import           Data.Hashable
import qualified Data.Text as T


traceFix     ::  (Fixpoint a) => String -> a -> a
traceFix s x = trace ("\nTrace: [" ++ s ++ "] : " ++ showFix x) x

------------------------------------------------------------------
class Fixpoint a where
  toFix    :: a -> Doc
  simplify :: a -> a
  simplify =  id

showFix :: (Fixpoint a) => a -> String
showFix =  render . toFix

instance (Eq a, Hashable a, Fixpoint a) => Fixpoint (S.HashSet a) where
  toFix xs = brackets $ sep $ punctuate (text ";") (toFix <$> S.toList xs)
  simplify = S.fromList . map simplify . S.toList

instance Fixpoint () where
  toFix _ = text "()"

instance Fixpoint a => Fixpoint (Maybe a) where
  toFix    = maybe (text "Nothing") ((text "Just" <+>) . toFix)
  simplify = fmap simplify

instance Fixpoint a => Fixpoint [a] where
  toFix xs = brackets $ sep $ punctuate (text ";") (fmap toFix xs)
  simplify = map simplify

instance (Fixpoint a, Fixpoint b) => Fixpoint (a,b) where
  toFix   (x,y)  = toFix x <+> text ":" <+> toFix y
  simplify (x,y) = (simplify x, simplify y)

instance (Fixpoint a, Fixpoint b, Fixpoint c) => Fixpoint (a,b,c) where
  toFix   (x,y,z)  = toFix x <+> text ":" <+> toFix y <+> text ":" <+> toFix  z
  simplify (x,y,z) = (simplify x, simplify y,simplify z)

instance Fixpoint Bool where
  toFix True  = text "True"
  toFix False = text "False"
  simplify z  = z

instance Fixpoint Int where
  toFix = tshow

instance Fixpoint Integer where
  toFix = integer

instance Fixpoint Double where
  toFix = double

------------------------------------------------------------------

data Tidy = Lossy | Full deriving (Eq, Ord)

class PPrint a where
  pprint :: a -> Doc
  pprint = pprintPrec 0

  -- | Pretty-print something with a specific precedence.
  pprintPrec :: Int -> a -> Doc
  pprintPrec _ = pprint

  pprintTidy :: Tidy -> a -> Doc
  pprintTidy _ = pprint


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
pprintKVs = vcat . punctuate (text "\n") . map pp1
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

instance PPrint T.Text where
  pprint = text . T.unpack

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
