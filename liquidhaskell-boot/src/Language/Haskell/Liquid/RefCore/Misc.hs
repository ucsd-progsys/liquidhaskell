-- | Functions used in the translation from Core and Spec
module Language.Haskell.Liquid.RefCore.Misc where

import Data.List (intercalate, stripPrefix, uncons, unfoldr)
import Data.Maybe (fromMaybe)
import GHC.Core
import Language.Haskell.Liquid.RefCore.Names (Id)

-- * Name manipulation

strip :: Id -> Id
strip s = case split '.' s of
  [] -> ""
  parts -> last parts

split :: Char -> Id -> [Id]
split c = unfoldr go
  where
    go [] = Nothing
    go s = Just (chunk, drop 1 rest)
      where
        (chunk, rest) = break (== c) s

startsWith :: Id -> Char -> Bool
startsWith xs c = maybe False ((== c) . fst) (uncons xs)

-- Get rid of module names.
showStripped :: (Show a) => a -> Id
showStripped = strip . show

-- | Remove character from LH names that are illegal in names for the translation
removeIllegalCharacters :: Id -> Id
removeIllegalCharacters = filter (not . (`elem` illegalChars))

illegalChars :: [Char]
illegalChars = ['$', '#']

-- | Remove illegal characters from LH names and strip their qualifications, unless this produces a built-in name
stripLegalName :: Id -> Id -> Id
stripLegalName moduleId s = removeIllegalCharacters $ if strip s `elem` rocqReservedNames then prefixedS else strip s
  where
    prefS = split '.' s
    -- \| Unfortunately Coq doesn't let us use "." prefixes in names, so we use "__" instead
    prefixedS = if length prefS > 1 then intercalate "__" . drop (length prefS - 2) $ prefS else stripLegalName "" (moduleId ++ "." ++ s) -- error $ "clashing:" ++ s

-- | Whether a String is a built-in datatype
isBuiltinDatatype :: Id -> Bool
isBuiltinDatatype tc = tc == "[]" || tc == "Maybe" || isTuple tc
  where
    isTuple ('(' : ',' : s) = isTuple' s
    isTuple _ = False
    isTuple' (',' : s) = isTuple' s
    isTuple' [')'] = True
    isTuple' _ = False

-- A non-exhaustive list of reserved names
rocqReservedNames :: [Id]
rocqReservedNames = [
  "Z", "bool", "Set", "Type", "Prop",
  "From", "Require", "Import", "Export", "Open", "Scope", "Z_scope", "Int_scope",
  "LiquidPreludeUtil", "Unicode",
  "Inductive", "Fixpoint", "Theorem", "Lemma", "Definition", "Hint",
  "Proof", "Qed", "Defined", "Opaque", "Transparent",
  "Resolve", "Global", "global", "Instance", "Notation", "Rewrite",
  "match", "with", "let", "in", "by", "end", "if", "then", "else"]

-- * GHC Core helpers

-- | tests whether an GHC bind starts with '$' or '?' and should thus not be translated
isIgnoredBind :: (Show b) => Bind b -> Bool
isIgnoredBind bind = name `startsWith` '$' || name == "?"
  where
    name = bindName bind
    bindName (NonRec b _) = showStripped b
    bindName (Rec ((b, _) : _)) = showStripped b
    bindName (Rec []) = "?"

-- * Generic list helpers

removeSuffix :: (Eq a) => [a] -> [a] -> [a]
removeSuffix suffix orig = reverse $ removePrefix (reverse suffix) (reverse orig)

removePrefix :: (Eq a) => [a] -> [a] -> [a]
removePrefix prefix orig = fromMaybe orig $ stripPrefix prefix orig
