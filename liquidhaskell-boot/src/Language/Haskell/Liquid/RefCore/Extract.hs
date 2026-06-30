{-# LANGUAGE OrPatterns #-}
{-# OPTIONS_GHC -Wall #-}

-- | Extracts Calculus declarations out of LiquidHaskell's TargetInfo + GHC core
--   binds.
module Language.Haskell.Liquid.RefCore.Extract
  ( SrcInfo (..)
  , CalcMeta (..)
  , OUT (..)
  , extractCalculus
  , writeIlh
  , writeOut
  , writeIlhBin
  , outPath
  ) where

import Control.Monad (unless)
import qualified Data.Binary as Bin
import Data.Bifunctor (bimap)
import Data.Char (isSpace)
import Data.List (intercalate, isPrefixOf)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.Directory (createDirectoryIfMissing, getCurrentDirectory)
import System.FilePath (joinPath, splitDirectories, takeDirectory, (</>))
import qualified Text.PrettyPrint.HughesPJClass as PP

import GHC.Core
import GHC.Plugins hiding (Id, split)
import qualified Language.Fixpoint.Types as F (Located, val)
import           Language.Fixpoint.Utils.Files (tempDirectory)
import           Language.Haskell.Liquid.Types.RType (SpecType, TyConP (..))
import qualified Language.Haskell.Liquid.Types.Specs as Specs
import           Language.Haskell.Liquid.Types.Types (AnnInfo (..))
import           Language.Haskell.Liquid.RefCore.Misc (isIgnoredBind, removeSuffix, split, stripLegalName)
import           Language.Haskell.Liquid.RefCore.Names (Id)
import qualified Language.Haskell.Liquid.RefCore.Calculus as Calc
import qualified Language.Haskell.Liquid.RefCore.CoreToLH as CLH
import           Language.Haskell.Liquid.RefCore.Parse
import           Language.Haskell.Liquid.RefCore.Simplify (simplify)
import qualified Language.Haskell.Liquid.RefCore.SpecToLH as SLH

-- | Contains all information about the source Liquid Haskell file to translate
data SrcInfo = SrcInfo
  { s_moduleName :: ModuleName
  , s_summary    :: ModSummary
  , s_targetInfo :: Specs.TargetInfo
  , s_cbs        :: [CoreBind]
    -- ^ Pre-'?'-elimination ANF binds, saved before 'Specs.giCbs' strips '?' for constraint generation.
  , s_infTypes   :: AnnInfo SpecType
  , s_imports    :: [Module]
  }

-- | Metadata about the extracted Calculus independent of LH/GHC types.
data CalcMeta = CalcMeta
  { cmTarget     :: FilePath
  , cmModuleName :: String
  }

-- | Extract the Calculus declarations for a module.
extractCalculus :: SrcInfo -> IO ([Calc.Decl], CalcMeta)
extractCalculus sinfo = do
    workingPath <- getCurrentDirectory
    let moduleId = takeWhile (not . isSpace) $ moduleNameString (s_moduleName sinfo)
        modulename = last $ split '.' moduleId
        examplesFolder = getSrcFolder moduleId filename workingPath
        target = workingPath </> filename
        pb = getBindsAndSpecs moduleId sinfo
        importNames = getModIdsAndImports sinfo
        localDecls = filterLocalPData (s_moduleName sinfo) (pb_decls pb)
        dataDecls = parsePData moduleId localDecls
        specMap = SLH.transSig moduleId Nothing <$> M.fromList (pb_specs pb)
        lhDefs = CLH.transBind moduleId (s_infTypes sinfo) . simplify <$> filter (not . isIgnoredBind) (pb_binds pb)
        defDecls = combineDefsAndLemmas $ pairLHDefsWithSigs moduleId lhDefs specMap (pb_vars pb)
        specSig = Specs.gsSig . Specs.giSpec $ s_targetInfo sinfo
        rawSpecs = Specs.gsTySigs specSig
        asmSpecs = Specs.gsAsmSigs specSig
        refSpecs = Specs.gsRefSigs specSig
        allSpecs = rawSpecs ++ asmSpecs ++ refSpecs
        importDecls = map (mkImportDecl moduleId (pb_decls pb) allSpecs) importNames
        -- Note: declarations are emitted in source order.
        calcSource = importDecls ++ dataDecls ++ defDecls
        meta = CalcMeta target modulename
    importedSourceFiles <- getImportFiles examplesFolder importNames
    putStrLn $ "Input file: " ++ filename
    unless (null importNames) $
      putStrLn ("Imported external files: " ++ intercalate ", " importedSourceFiles)
    pure (calcSource, meta)
  where
    filename = Specs.giTarget $ Specs.giSrc $ s_targetInfo sinfo

-- | Output formats for the un-elaborated Calculus produced by extraction.
data OUT = Text | Bin
  deriving (Show)

outPostfix :: OUT -> String
outPostfix Text = ".ilh"
outPostfix Bin = ".ilhb"

-- | The .liquid folder for the .ilh/.ilhb files.
binFolder :: CalcMeta -> FilePath
binFolder = tempDirectory . cmTarget

-- | Write the un-elaborated Calculus declarations to the .ilh text file.
writeIlh :: CalcMeta -> [Calc.Decl] -> IO ()
writeIlh meta calcSource = do
    createDirectoryIfMissing True (binFolder meta)
    writeOut (binFolder meta) (cmModuleName meta) (outPostfix Text) PP.empty calcSource

-- | Path of .ilh/.ilhb in the .liquid folder.
outPath :: OUT -> CalcMeta -> FilePath
outPath out meta = binFolder meta </> (cmModuleName meta ++ outPostfix out)

writeIlhBin :: CalcMeta -> [Calc.Decl] -> IO ()
writeIlhBin meta calcSource = do
    createDirectoryIfMissing True (binFolder meta)
    let path = outPath Bin meta
    putStrLn ("Writing serialized Calculus to " ++ path)
    Bin.encodeFile path calcSource

-- | Pretty-print a list of declarations to a file with the given filename
--   suffix.
writeOut :: (PP.Pretty a) => FilePath -> String -> String -> PP.Doc -> [a] -> IO ()
writeOut outputFolder modulename suffix pre decls = do
    let outputPath = outputFolder </> (modulename ++ suffix)
    putStrLn ("Writing output to file at " ++ outputPath)
    let body = PP.vcat (pre PP.<> PP.char '\n' : map ((PP.<> PP.char '\n') . PP.pPrint) decls)
        style = PP.Style {PP.mode = PP.PageMode, PP.lineLength = 120, PP.ribbonsPerLine = 1.2}
    writeFile outputPath (PP.renderStyle style body)
    putStrLn ""

-- | Parsed binds and specs extracted from LH.
data ParsedBinds = ParsedBinds
  { pb_src   :: Specs.TargetSrc
  , pb_vars  :: [Var]
  , pb_decls :: PData
  , pb_binds :: [CoreBind]
  , pb_specs :: [SpecPair]
  }

getBindsAndSpecs :: Id -> SrcInfo -> ParsedBinds
getBindsAndSpecs modId sinfo = ParsedBinds
        { pb_src = src
        , pb_vars = refls
        , pb_decls = getDataDecls (Specs.gsData specs, Specs.gsName specs)
        , pb_binds = s_cbs sinfo
        , pb_specs = getSpecPairs specs
        }
  where
    Specs.TargetInfo src specs = s_targetInfo sinfo
    refls = Specs.gsReflects $ Specs.gsRefl specs
    getSpecPairs = map (bimap (stripLegalName modId . show) F.val) . Specs.gsTySigs . Specs.gsSig
    getDataDecls (spdata, spnames) = PData (Specs.gsCtors spdata) (Specs.gsTconsP spnames)

getSrcPath :: String -> String -> String -> [String]
getSrcPath moduleId filename workingPath = removeSuffix modulePrefixes folderPath where
    modulePrefixes = init $ split '.' moduleId
    folderPath = splitDirectories $ takeDirectory (workingPath </> filename)

getSrcFolder :: String -> String -> String -> FilePath
getSrcFolder moduleId filename workingPath = joinPath (getSrcPath moduleId filename workingPath)

getModIdsAndImports :: SrcInfo -> [String]
getModIdsAndImports sinfo = map modNameString $ filter (not . isStdLibModule) (s_imports sinfo)
  where
    modNameString = moduleNameString . moduleName
    isStdLibModule m = any (`isPrefixOf` modNameString m) stdLibPrefixes
    stdLibPrefixes = ["GHC.", "Data.", "Control.", "System.", "Prelude", "Foreign.", "Text.", "Numeric.", "Language."]

-- | The defining module name of a type constructor, if any.
tyConPModule :: TyConP -> Maybe ModuleName
tyConPModule tcp = moduleName <$> nameModule_maybe (tyConName (tcpCon tcp))

-- | The defining module name of a variable, if any.
varModule :: Var -> Maybe ModuleName
varModule v = moduleName <$> nameModule_maybe (varName v)

-- | Whether a type constructor is defined in the named module.
tyConPFromModule :: String -> TyConP -> Bool
tyConPFromModule modStr tcp = maybe False ((== modStr) . moduleNameString) (tyConPModule tcp)

-- | Whether a variable is defined in the named module.
varFromModule :: String -> Var -> Bool
varFromModule modStr v = maybe False ((== modStr) . moduleNameString) (varModule v)

filterLocalPData :: ModuleName -> PData -> PData
filterLocalPData modName pd = pd {pdTyCons = filteredTyCons, pdCtors = filteredCtors}
  where
    filteredTyCons = filter isLocalTC (pdTyCons pd)
    filteredCtors = filter (isLocalCtor . fst) (pdCtors pd)
    isLocalTC tcp = maybe True (== modName) (tyConPModule tcp)
    isLocalCtor v = maybe True (== modName) (varModule v)

filterPDataForModule :: String -> PData -> PData
filterPDataForModule modStr pd =
  pd {pdTyCons = filter (tyConPFromModule modStr) (pdTyCons pd), pdCtors = filter (varFromModule modStr . fst) (pdCtors pd)}

mkImportDecl :: Id -> PData -> [(Var, F.Located SpecType)] -> String -> Calc.Decl
mkImportDecl moduleId allPData rawSpecs modName = Calc.Import modName (dataDs ++ defDs)
  where
    dataDs = parsePData moduleId (filterPDataForModule modName allPData)
    defDs = map mkDefStub $ filter (varFromModule modName . fst) rawSpecs
    mkDefStub (v, locSpec) =
      Calc.Definition
        (stripLegalName moduleId (show (varName v)))
        (SLH.transSig moduleId Nothing (F.val locSpec))
        (Calc.Reft (Calc.Var "imported" Nothing Calc.Global))
        False

pairLHDefsWithSigs :: Id -> [CLH.Def] -> M.Map Id Calc.RefType -> [Var] -> [(CLH.Def, Maybe Calc.RefType, Bool)]
pairLHDefsWithSigs modId defs specMap reflectedDecls = map single defs
  where
    reflectedNames :: S.Set Id
    reflectedNames = S.fromList $ map (stripLegalName modId . show . varName) reflectedDecls
    single def = (def, M.lookup (CLH.defName def) specMap, CLH.defName def `S.member` reflectedNames)
