{-# OPTIONS_GHC -Wall #-}

module Language.Haskell.Liquid.RefCore.Parse
  ( -- ** type aliases for intermediate data
    SpecPair,
    PData (..),

    -- ** "parsers" for the specification data extracted from LH
    parseToSpecPair,
    parsePData,

    -- ** combine "parsed" LH specification data with GHC
    getImportFiles,
    combineDefsAndLemmas,

    -- ** utility function
    signatureToArgsRet,
  )
where

import Control.Monad (filterM)
-- import GHC.Core.DataCon
import Data.Bifunctor (first)
import Data.List (sortOn)
import Data.Set (fromList)
import Data.Tuple.Extra (snd3)
import System.Directory (doesFileExist)
import System.FilePath (joinPath, (<.>), (</>))

import GHC.Types.Var (Var, varName)
import qualified Language.Fixpoint.Types as F (Located (..))
import qualified Language.Haskell.Liquid.Types.RType as LhLib

import           Language.Haskell.Liquid.RefCore.Misc
import           Language.Haskell.Liquid.RefCore.Names (Id, freshVar)
import qualified Language.Haskell.Liquid.RefCore.Calculus as Calc
import qualified Language.Haskell.Liquid.RefCore.SpecToLH as SLH
import           Language.Haskell.Liquid.RefCore.CoreToLH (Def (..))

-- ** LH -> Calculus parsing

type SpecPair = (Id, LhLib.SpecType)

-- | Parsed data declarations extracted from Liquid Haskell
data PData = PData
  { -- | refined types of data constructors
    pdCtors :: [(Var, F.Located LhLib.SpecType)],
    -- | refined types of type constructors
    pdTyCons :: [LhLib.TyConP]
  }

-- , [LhLib.Located DataCon], [F.DataDecl]) -- more data type info, in case they are needed
parseToSpecPair :: Id -> (Var, F.Located LhLib.SpecType) -> SpecPair
parseToSpecPair modId (v, F.Loc _ _ spec) = (stripLegalName modId $ show (varName v), spec)

-- | Parse refined type constructors into Calculus declarations
parsePData :: Id -> PData -> [Calc.Decl]
parsePData modId (PData cs typConstrs) =
  {- trace ("parsePData " ++ modId ++ "\n("++show constrs++", "++show typConstrs++")") $ -}
  map mkData (filter (not . isBuiltinDatatype) typeNames)
  where
    -- translate each branch
    constrs :: [(Id, Calc.RefType)]
    constrs = map (parseSpec . parseToSpecPair modId) cs
    parseSpec (c, sig) =
      let sigT = SLH.transSig modId (Just c) sig
          (args', ret) = signatureToArgsRet sigT
          args_ = map defaultBind args'
          args = mkDistinct args_
       in (c, foldr (\(n, t) acc -> Calc.ArrType n t acc) ret args)
    mkDistinct [] = []
    mkDistinct ((x, xData) : tl) = (x, xData) : mkDistinct (map (first (\y -> if y == x then y ++ "_" else y)) tl)
    -- we translate every type constructor that is not already built-in
    typeNames = map (\(LhLib.TyConP _ con _ _ _ _ _) -> SLH.showppStripped modId con) typConstrs
    -- find the translated branches corresponding to typeName
    getConstrs :: Id -> [(Id, Calc.RefType)]
    getConstrs typeName = filter (isConstrOf typeName . snd3 . snd . Calc.arrs . snd) constrs
    isConstrOf typeName (Calc.TC n) = n == typeName
    isConstrOf _ (Calc.Builtin _) = False
    -- Assemble typeName and the corresponding translated branches
    mkData typeName = Calc.Data typeName (sortOn fst (getConstrs typeName))

-- ** translating the intermediate data structures to 'Calc.Decl's

-- | combine the defs and lemmas into a list of 'Calc.Decl' and sort them in dependency order
combineDefsAndLemmas :: [(Def, Maybe Calc.RefType, Bool)] -> [Calc.Decl]
combineDefsAndLemmas = map parseDef

-- | compute the file path of the module with given name
getImportFile :: FilePath -> String -> FilePath
getImportFile examplesFolder moduleName = examplesFolder </> joinPath (split '.' moduleName) <.> "hs"

-- | filter out only those imported module names that correspond to files in the lhExamples folder
filterImports :: String -> [String] -> IO [String]
filterImports examplesFolder =
  filterM (doesFileExist . getImportFile examplesFolder)

-- | Get the imported filenames and the import declarations for the specified module names
getImportFiles :: String -> [String] -> IO [String]
getImportFiles examplesFolder potentialImports =
  map (getImportFile examplesFolder) <$> filterImports examplesFolder potentialImports

isLemma :: Calc.RefType -> Bool
isLemma = (== "()") . typeName . snd3 . snd . Calc.arrs
  where
    typeName :: Calc.BaseType -> String
    typeName (Calc.Builtin c) = show c
    typeName (Calc.TC n) = n

parseDef :: (Def, Maybe Calc.RefType, Bool) -> Calc.Decl
parseDef (Def dname args body _, Just sig, b) =
  Calc.Definition dname fullTp body b
  where
    sig' = Calc.renameParams args sig
    (sigArgs, sRes) = signatureToArgsRet sig'
    tp =
      if isLemma sig'
        then case sRes of
          Calc.RefType _ _ reft -> Calc.RefType (dname ++ "_claim") Calc.unitTp reft
          _ -> error $ "Lemma " ++ dname ++ " has unexpected arrow return type"
        else sRes

    fullTp = foldr (\(n, t) acc -> Calc.ArrType n t acc) tp (zip args sigArgs)
parseDef (Def dname _ _ _, Nothing, _) = error $ "Top-level definition or lemma " ++ dname ++ " without signature is forbidden."

-- | replace the names of variables v in refinement types {v:A|p} of arguments x by x
signatureToArgsRet :: Calc.RefType -> ([Calc.RefType], Calc.RefType)
signatureToArgsRet sig = (args, ret)
  where
    (sigArgs, (v0, sResTp, sResReft)) = Calc.arrs sig
    names = map fst sigArgs
    v = freshVar v0 (fromList names)
    ret = Calc.RefType v sResTp $ Calc.subst (Calc.mkVar v) v0 sResReft
    args = map renameArg sigArgs
    renameArg (n, Calc.RefType x tp reft) = Calc.RefType m tp (Calc.subst (Calc.mkVar m) x reft)
      where
        m = if n /= "" then n else x
    renameArg (_, arr@Calc.ArrType {}) = arr

-- > defaultBind({x:A | r})  = (x, {x:A | r})
-- > defaultBind(x: Tx -> Y) = (x, (x: Tx -> Y)
defaultBind :: Calc.RefType -> (Id, Calc.RefType)
defaultBind r@(Calc.RefType nm _ _) = (nm, r)
defaultBind a@(Calc.ArrType nm _ _) = (nm, a)

