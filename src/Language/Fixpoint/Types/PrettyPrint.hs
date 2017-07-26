{-# LANGUAGE CPP                #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverloadedStrings  #-}

module Language.Fixpoint.Types.PrettyPrint where

import           Debug.Trace               (trace)
import           Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.Boxes as B
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L
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

instance (Ord a, Hashable a, Fixpoint a) => Fixpoint (S.HashSet a) where
  toFix xs = brackets $ sep $ punctuate ";" (toFix <$> L.sort (S.toList xs))
  simplify = S.fromList . map simplify . S.toList

instance Fixpoint () where
  toFix _ = "()"

instance Fixpoint a => Fixpoint (Maybe a) where
  toFix    = maybe "Nothing" (("Just" <+>) . toFix)
  simplify = fmap simplify

instance Fixpoint a => Fixpoint [a] where
  toFix xs = brackets $ sep $ punctuate ";" (fmap toFix xs)
  simplify = map simplify

instance (Fixpoint a, Fixpoint b) => Fixpoint (a,b) where
  toFix   (x,y)  = toFix x <+> ":" <+> toFix y
  simplify (x,y) = (simplify x, simplify y)

instance (Fixpoint a, Fixpoint b, Fixpoint c) => Fixpoint (a,b,c) where
  toFix   (x,y,z)  = toFix x <+> ":" <+> toFix y <+> ":" <+> toFix  z
  simplify (x,y,z) = (simplify x, simplify y,simplify z)

instance Fixpoint Bool where
  toFix True  = "True"
  toFix False = "False"
  simplify z  = z

instance Fixpoint Int where
  toFix = tshow

instance Fixpoint Integer where
  toFix = integer

instance Fixpoint Double where
  toFix = double

------------------------------------------------------------------

data Tidy = Lossy | Full deriving (Eq, Ord)

-- | Implement either `pprintTidy` or `pprintPrec`
class PPrint a where

  pprintTidy :: Tidy -> a -> Doc
  pprintTidy = pprintPrec 0

  pprintPrec :: Int -> Tidy -> a -> Doc
  pprintPrec _ = pprintTidy

-- | Top-level pretty printer
pprint :: (PPrint a) => a -> Doc
pprint = pprintPrec 0 Full

showpp :: (PPrint a) => a -> String
showpp = render . pprint

showTable :: (PPrint k, PPrint v) => Tidy -> [(k, v)] -> String
showTable k = render . pprintKVs k

-- | Please do not alter this.
tracepp :: (PPrint a) => String -> a -> a
tracepp s x = trace ("\nTrace: [" ++ s ++ "] : " ++ showpp x) x

notracepp :: (PPrint a) => String -> a -> a
notracepp _ x = x

instance PPrint Doc where
  pprintTidy _ = id

instance PPrint a => PPrint (Maybe a) where
  pprintTidy k = maybe "Nothing" (("Just" <+>) . pprintTidy k)

instance PPrint a => PPrint [a] where
  pprintTidy k = brackets . sep . punctuate comma . map (pprintTidy k)

instance PPrint a => PPrint (S.HashSet a) where
  pprintTidy k = pprintTidy k . S.toList

instance (PPrint a, PPrint b) => PPrint (M.HashMap a b) where
  pprintTidy k = pprintKVs k . M.toList

pprintKVs   :: (PPrint k, PPrint v) => Tidy -> [(k, v)] -> Doc
pprintKVs t = vcat . punctuate "\n" . map pp1
  where
    pp1 (x,y) = pprintTidy t x <+> ":=" <+> pprintTidy t y

instance (PPrint a, PPrint b, PPrint c) => PPrint (a, b, c) where
  pprintTidy k (x, y, z)  = parens $ pprintTidy k x <> "," <+>
                                     pprintTidy k y <> "," <+>
                                     pprintTidy k z



instance (PPrint a, PPrint b, PPrint c, PPrint d) => PPrint (a, b, c, d) where
  pprintTidy k (w, x, y, z)  = parens $ pprintTidy k w <> "," <+>
                                        pprintTidy k x <> "," <+>
                                        pprintTidy k y <> "," <+>
                                        pprintTidy k z

instance (PPrint a, PPrint b, PPrint c, PPrint d, PPrint e) => PPrint (a, b, c, d, e) where
  pprintTidy k (v, w, x, y, z)  = parens $ pprintTidy k v <> "," <+>
                                           pprintTidy k w <> "," <+>
                                           pprintTidy k x <> "," <+>
                                           pprintTidy k y <> "," <+>
                                           pprintTidy k z



instance (PPrint a, PPrint b) => PPrint (a,b) where
  pprintTidy k (x, y)  = pprintTidy k x <+> ":" <+> pprintTidy k y

instance PPrint Bool where
  pprintTidy _ = text . show

instance PPrint Float where
  pprintTidy _ = text . show

instance PPrint () where
  pprintTidy _ = text . show

#if !(defined(MIN_VERSION_GLASGOW_HASKELL) && (MIN_VERSION_GLASGOW_HASKELL(8,0,1,1)))
instance PPrint String where
  pprintTidy _ = text
#endif

instance PPrint Int where
  pprintTidy _ = tshow

instance PPrint Integer where
  pprintTidy _ = integer

instance PPrint T.Text where
  pprintTidy _ = text . T.unpack

newtype DocTable = DocTable [(Doc, Doc)]

instance Monoid DocTable where
  mempty                              = DocTable []
  mappend (DocTable t1) (DocTable t2) = DocTable (t1 ++ t2)

class PTable a where
  ptable :: a -> DocTable

instance PPrint DocTable where
  pprintTidy _ (DocTable kvs) = boxDoc $ B.hsep 1 B.left [ks', cs', vs']
    where
      (ks, vs)                = unzip kvs
      n                       = length kvs
      ks'                     = B.vcat B.left  $ docBox <$> ks
      vs'                     = B.vcat B.right $ docBox <$> vs
      cs'                     = B.vcat B.left  $ replicate n $ B.text ":"

boxHSep :: Doc -> Doc -> Doc
boxHSep d1 d2 = boxDoc $ B.hcat B.top [docBox d1, docBox d2]

boxDoc :: B.Box -> Doc
boxDoc = text . B.render

docBox :: Doc -> B.Box
docBox = B.text . render
