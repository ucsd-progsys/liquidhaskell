-- This script processes the following source file:
--
--   http://unicode.org/Public/UNIDATA/CaseFolding.txt

module CaseFolding
    (
      Fold(..)
    , parseCF
    , mapCF
    ) where

import Arsec

data Fold = Fold {
      code :: Char
    , status :: Char
    , mapping :: [Char]
    , name :: String
    } deriving (Eq, Ord, Show)

entries :: Parser [Fold]
entries = many comment *> many (entry <* many comment)
  where
    entry = Fold <$> unichar <* semi
                 <*> oneOf "CFST" <* semi
                 <*> unichars
                 <*> (string "# " *> manyTill anyToken (char '\n'))

parseCF :: FilePath -> IO (Either ParseError [Fold])
parseCF name = parse entries name <$> readFile name

mapCF :: [Fold] -> [String]
mapCF ms = typ ++ (map nice . filter p $ ms) ++ [last]
  where
    typ = ["foldMapping :: forall s. Char -> s -> Step (CC s) Char"
           ,"{-# INLINE foldMapping #-}"]
    last = "foldMapping c s = Yield (toLower c) (CC s '\\0' '\\0')"
    nice c = "-- " ++ name c ++ "\n" ++
             "foldMapping " ++ showC (code c) ++ " s = Yield " ++ x ++ " (CC s " ++ y ++ " " ++ z ++ ")"
       where [x,y,z] = (map showC . take 3) (mapping c ++ repeat '\0')
    p f = status f `elem` "CF" &&
          mapping f /= [toLower (code f)]
