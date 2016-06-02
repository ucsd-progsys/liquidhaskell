{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}

{- LIQUID "--diffcheck" @-}

---------------------------------------------------------------------------
-- | This module contains the code that uses the inferred types to generate
-- 1. HTMLized source with Inferred Types in mouseover annotations.
-- 2. Annotations files (e.g. for vim/emacs)
-- 3. JSON files for the web-demo etc.
---------------------------------------------------------------------------


module Language.Haskell.Liquid.UX.Annotate (specAnchor, mkOutput, annotate) where

import           Data.Hashable
import           Data.String
import           GHC                                          ( SrcSpan (..)
                                          , srcSpanStartCol
                                          , srcSpanEndCol
                                          , srcSpanStartLine
                                          , srcSpanEndLine)
import           GHC.Exts                                     (groupWith, sortWith)
import           Prelude                                      hiding (error)
import qualified SrcLoc
import           Text.PrettyPrint.HughesPJ                    hiding (first)
import           Text.Printf

import           Data.Char                                    (isSpace)
import           Data.Function                                (on)
import           Data.List                                    (sortBy)
import           Data.Maybe                                   (mapMaybe)

import           Data.Aeson
import           Control.Arrow                                hiding ((<+>))
-- import           Control.Applicative      ((<$>))
import           Control.Monad                                (when, forM_)

import           System.Exit                                  (ExitCode (..))
import           System.FilePath                              (takeFileName, dropFileName, (</>))
import           System.Directory                             (findExecutable, copyFile)
import qualified Data.List                                    as L
import qualified Data.Vector                                  as V
import qualified Data.ByteString.Lazy                         as B
import qualified Data.Text                                    as T
import qualified Data.HashMap.Strict                          as M
import qualified Language.Haskell.Liquid.UX.ACSS              as ACSS
import           Language.Haskell.HsColour.Classify
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Misc
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Fixpoint.Types                      hiding (Error, Loc, Constant (..), Located (..))
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types.PrettyPrint
import           Language.Haskell.Liquid.Types.RefType

import           Language.Haskell.Liquid.UX.Errors            ()
import           Language.Haskell.Liquid.UX.Tidy
import           Language.Haskell.Liquid.Types                hiding (Located(..), Def(..))
import           Language.Haskell.Liquid.Types.Specifications


-- | @output@ creates the pretty printed output
--------------------------------------------------------------------------------------------
mkOutput :: Config -> ErrorResult -> FixSolution -> AnnInfo (Annot SpecType) -> Output Doc
--------------------------------------------------------------------------------------------
mkOutput cfg res sol anna
  = O { o_vars   = Nothing
      , o_errors = []
      , o_types  = toDoc <$> annTy
      , o_templs = toDoc <$> annTmpl
      , o_bots   = mkBots    annTy
      , o_result = res
      }
  where
    annTmpl      = closeAnnots anna
    annTy        = tidySpecType Lossy <$> applySolution sol annTmpl
    toDoc        = rtypeDoc tidy
    tidy         = if shortNames cfg then Lossy else Full

-- | @annotate@ actually renders the output to files
-------------------------------------------------------------------
annotate :: Config -> [FilePath] -> Output Doc -> IO ACSS.AnnMap
-------------------------------------------------------------------
annotate cfg srcFs out
  = do when showWarns $ forM_ bots (printf "WARNING: Found false in %s\n" . showPpr)
       mapM_ (doGenerate cfg tplAnnMap typAnnMap annTyp) srcFs
       return typAnnMap
    where
       tplAnnMap  = mkAnnMap cfg res annTpl
       typAnnMap  = mkAnnMap cfg res annTyp
       annTpl     = o_templs out
       annTyp     = o_types  out
       res        = o_result out
       bots       = o_bots   out
       showWarns  = not $ nowarnings cfg

doGenerate :: Config -> ACSS.AnnMap -> ACSS.AnnMap -> AnnInfo Doc -> FilePath -> IO ()
doGenerate cfg tplAnnMap typAnnMap annTyp srcF
  = do generateHtml srcF tpHtmlF tplAnnMap
       generateHtml srcF tyHtmlF typAnnMap
       writeFile         vimF  $ vimAnnot cfg annTyp
       B.writeFile       jsonF $ encode typAnnMap
    where
       tyHtmlF    = extFileName Html                   srcF
       tpHtmlF    = extFileName Html $ extFileName Cst srcF
       _annF      = extFileName Annot srcF
       jsonF      = extFileName Json  srcF
       vimF       = extFileName Vim   srcF

mkBots :: Reftable r => AnnInfo (RType c tv r) -> [GHC.SrcSpan]
mkBots (AI m) = [ src | (src, (Just _, t) : _) <- sortBy (compare `on` fst) $ M.toList m
                      , isFalse (rTypeReft t) ]

writeFilesOrStrings :: FilePath -> [Either FilePath String] -> IO ()
writeFilesOrStrings tgtFile = mapM_ $ either (`copyFile` tgtFile) (tgtFile `appendFile`)

generateHtml :: FilePath -> FilePath -> ACSS.AnnMap -> IO ()
generateHtml srcF htmlF annm
  = do src     <- readFile srcF
       let lhs  = isExtFile LHs srcF
       let body = {-# SCC "hsannot" #-} ACSS.hsannot False (Just tokAnnot) lhs (src, annm)
       cssFile <- getCssPath
       copyFile cssFile (dropFileName htmlF </> takeFileName cssFile)
       renderHtml lhs htmlF srcF (takeFileName cssFile) body

renderHtml :: Bool -> FilePath -> [Char] -> [Char] -> [Char] -> IO ()
renderHtml True  = renderPandoc
renderHtml False = renderDirect

-------------------------------------------------------------------------
-- | Pandoc HTML Rendering (for lhs + markdown source) ------------------
-------------------------------------------------------------------------

renderPandoc :: FilePath -> [Char] -> [Char] -> [Char] -> IO ()
renderPandoc htmlFile srcFile css body
  = do renderFn <- maybe renderDirect renderPandoc' <$> findExecutable "pandoc"
       renderFn htmlFile srcFile css body

renderPandoc' :: PrintfArg t
              => t -> FilePath -> FilePath -> [Char] -> String -> IO ()
renderPandoc' pandocPath htmlFile srcFile css body
  = do _  <- writeFile mdFile $ pandocPreProc body
       ec <- executeShellCommand "pandoc" cmd
       writeFilesOrStrings htmlFile [Right (cssHTML css)]
       checkExitCode cmd ec
    where mdFile = extFileName Mkdn srcFile
          cmd    = pandocCmd pandocPath mdFile htmlFile

checkExitCode :: Monad m => [Char] -> ExitCode -> m ()
checkExitCode _   (ExitSuccess)   = return ()
checkExitCode cmd (ExitFailure n) = panic Nothing $ "cmd: " ++ cmd ++ " failure code " ++ show n

pandocCmd :: (PrintfArg t1, PrintfArg t2, PrintfArg t3, PrintfType t)
          => t1 -> t2 -> t3 -> t
pandocCmd pandocPath mdFile htmlFile
  = printf "%s -f markdown -t html %s > %s" pandocPath mdFile htmlFile

pandocPreProc :: String -> String
pandocPreProc  = T.unpack
               . strip beg code
               . strip end code
               . strip beg spec
               . strip end spec
               . T.pack
  where
    beg, end, code, spec :: String
    beg        = "begin"
    end        = "end"
    code       = "code"
    spec       = "spec"
    strip x y  = T.replace (T.pack $ printf "\\%s{%s}" x y) T.empty
    -- stripBcode = T.replace (T.pack "\\begin{code}") T.empty
    -- stripEcode = T.replace (T.pack "\\end{code}")   T.empty
    -- stripBspec = T.replace (T.pack "\\begin{code}") T.empty
    -- stripEspec = T.replace (T.pack "\\end{code}")   T.empty




-------------------------------------------------------------------------
-- | Direct HTML Rendering (for non-lhs/markdown source) ----------------
-------------------------------------------------------------------------

-- More or less taken from hscolour

renderDirect :: FilePath -> [Char] -> [Char] -> [Char] -> IO ()
renderDirect htmlFile srcFile css body
  = writeFile htmlFile $! (top'n'tail full srcFile css $! body)
    where full = True -- False  -- TODO: command-line-option

-- | @top'n'tail True@ is used for standalone HTML,
--   @top'n'tail False@ for embedded HTML

top'n'tail :: Bool -> [Char] -> [Char] -> [Char] -> [Char]
top'n'tail True  title css = (htmlHeader title css ++) . (++ htmlClose)
top'n'tail False _    _    = id

-- Use this for standalone HTML

htmlHeader :: [Char] -> [Char] -> String
htmlHeader title css = unlines
  [ "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 3.2 Final//EN\">"
  , "<html>"
  , "<head>"
  , "<title>" ++ title ++ "</title>"
  , "</head>"
  , cssHTML css
  , "<body>"
  , "<hr>"
  , "Put mouse over identifiers to see inferred types"
  ]

htmlClose :: IsString a => a
htmlClose  = "\n</body>\n</html>"

cssHTML :: [Char] -> String
cssHTML css = unlines
  [ "<head>"
  , "<link type='text/css' rel='stylesheet' href='"++ css ++ "' />"
  , "</head>"
  ]

------------------------------------------------------------------------------
-- | Building Annotation Maps ------------------------------------------------
------------------------------------------------------------------------------

-- | This function converts our annotation information into that which
--   is required by `Language.Haskell.Liquid.ACSS` to generate mouseover
--   annotations.

mkAnnMap :: Config -> ErrorResult -> AnnInfo Doc -> ACSS.AnnMap
mkAnnMap cfg res ann     = ACSS.Ann (mkAnnMapTyp cfg ann) (mkAnnMapErr res) (mkStatus res)

mkStatus :: FixResult t -> ACSS.Status
mkStatus (Safe)          = ACSS.Safe
mkStatus (Unsafe _)      = ACSS.Unsafe
mkStatus (Crash _ _)     = ACSS.Error



mkAnnMapErr :: PPrint (TError t)
            => FixResult (TError t) -> [(Loc, Loc, String)]
mkAnnMapErr (Unsafe ls)  = mapMaybe cinfoErr ls
mkAnnMapErr (Crash ls _) = mapMaybe cinfoErr ls
mkAnnMapErr _            = []

cinfoErr :: PPrint (TError t) => TError t -> Maybe (Loc, Loc, String)
cinfoErr e = case pos e of
               RealSrcSpan l -> Just (srcSpanStartLoc l, srcSpanEndLoc l, showpp e)
               _             -> Nothing


-- mkAnnMapTyp :: (RefTypable a c tv r, RefTypable a c tv (), PPrint tv, PPrint a) =>Config-> AnnInfo (RType a c tv r) -> M.HashMap Loc (String, String)
mkAnnMapTyp :: Config -> AnnInfo Doc -> M.HashMap Loc (String, String)
mkAnnMapTyp cfg z = M.fromList $ map (first srcSpanStartLoc) $ mkAnnMapBinders cfg z

mkAnnMapBinders :: Config
                -> AnnInfo Doc -> [(SrcLoc.RealSrcSpan, (String, String))]
mkAnnMapBinders cfg (AI m)
  = map (second bindStr . head . sortWith (srcSpanEndCol . fst))
  $ groupWith (lineCol . fst) locBinds
  where
    locBinds       = [ (l, x) | (RealSrcSpan l, x:_) <- M.toList m, oneLine l]
    bindStr (x, v) = (maybe "_" (symbolString . shorten . symbol) x, render v)
    shorten        = if shortNames cfg then dropModuleNames else id

closeAnnots :: AnnInfo (Annot SpecType) -> AnnInfo SpecType
closeAnnots = closeA . filterA . collapseA

closeA :: AnnInfo (Annot b) -> AnnInfo b
closeA a@(AI m)   = cf <$> a
  where
    cf (AnnLoc l)  = case m `mlookup` l of
                      [(_, AnnUse t)] -> t
                      [(_, AnnDef t)] -> t
                      [(_, AnnRDf t)] -> t
                      _               -> panic Nothing $ "malformed AnnInfo: " ++ showPpr l
    cf (AnnUse t) = t
    cf (AnnDef t) = t
    cf (AnnRDf t) = t

filterA :: AnnInfo (Annot t) -> AnnInfo (Annot t)
filterA (AI m) = AI (M.filter ff m)
  where
    ff [(_, AnnLoc l)] = l `M.member` m
    ff _               = True

collapseA :: AnnInfo (Annot t) -> AnnInfo (Annot t)
collapseA (AI m) = AI (fmap pickOneA m)

pickOneA :: [(t, Annot t1)] -> [(t, Annot t1)]
pickOneA xas = case (rs, ds, ls, us) of
                 (x:_, _, _, _) -> [x]
                 (_, x:_, _, _) -> [x]
                 (_, _, x:_, _) -> [x]
                 (_, _, _, x:_) -> [x]
                 (_, _, _, _  ) -> [ ]
  where
    rs = [x | x@(_, AnnRDf _) <- xas]
    ds = [x | x@(_, AnnDef _) <- xas]
    ls = [x | x@(_, AnnLoc _) <- xas]
    us = [x | x@(_, AnnUse _) <- xas]

------------------------------------------------------------------------------
-- | Tokenizing Refinement Type Annotations in @-blocks ----------------------
------------------------------------------------------------------------------

-- | The token used for refinement symbols inside the highlighted types in @-blocks.
refToken :: TokenType
refToken = Keyword

-- | The top-level function for tokenizing @-block annotations. Used to
-- tokenize comments by ACSS.
tokAnnot :: [Char] -> [(TokenType, String)]
tokAnnot s
  = case trimLiquidAnnot s of
      Just (l, body, r) -> [(refToken, l)] ++ tokBody body ++ [(refToken, r)]
      Nothing           -> [(Comment, s)]

trimLiquidAnnot :: [Char] -> Maybe (String, [Char], String)
trimLiquidAnnot ('{':'-':'@':ss)
  | drop (length ss - 3) ss == "@-}"
  = Just (liquidBegin, take (length ss - 3) ss, liquidEnd)
trimLiquidAnnot _
  = Nothing

tokBody :: String -> [(TokenType, String)]
tokBody s
  | isData s  = tokenise s
  | isType s  = tokenise s
  | isIncl s  = tokenise s
  | isMeas s  = tokenise s
  | otherwise = tokeniseSpec s

isMeas :: String -> Bool
isMeas = spacePrefix "measure"

isData :: String -> Bool
isData = spacePrefix "data"

isType :: String -> Bool
isType = spacePrefix "type"

isIncl :: String -> Bool
isIncl = spacePrefix "include"

{-@ spacePrefix :: String -> s:String -> Bool / [len s] @-}
spacePrefix :: String -> String -> Bool
spacePrefix str s@(c:cs)
  | isSpace c   = spacePrefix str cs
  | otherwise   = take (length str) s == str
spacePrefix _ _ = False


tokeniseSpec       ::  String -> [(TokenType, String)]
tokeniseSpec str   = {- traceShow ("tokeniseSpec: " ++ str) $ -} tokeniseSpec' str

tokeniseSpec' :: String -> [(TokenType, String)]
tokeniseSpec'      = tokAlt . chopAltDBG -- [('{', ':'), ('|', '}')]
  where
    tokAlt (s:ss)  = tokenise s ++ tokAlt' ss
    tokAlt _       = []
    tokAlt' (s:ss) = (refToken, s) : tokAlt ss
    tokAlt' _      = []

chopAltDBG :: String -> [[Char]]
chopAltDBG y = {- traceShow ("chopAlts: " ++ y) $ -}
  filter (/= "") $ concatMap (chopAlts [("{", ":"), ("|", "}")])
  $ chopAlts [("<{", "}>"), ("{", "}")] y




------------------------------------------------------------------------
-- | JSON: Annotation Data Types ---------------------------------------
------------------------------------------------------------------------

data Assoc k a = Asc (M.HashMap k a)
type AnnTypes  = Assoc Int (Assoc Int Annot1)
type AnnErrors = [(Loc, Loc, String)]
data Annot1    = A1  { ident :: String
                     , ann   :: String
                     , row   :: Int
                     , col   :: Int
                     }

------------------------------------------------------------------------
-- | Creating Vim Annotations ------------------------------------------
------------------------------------------------------------------------

vimAnnot     :: Config -> AnnInfo Doc -> String
vimAnnot cfg = L.intercalate "\n" . map vimBind . mkAnnMapBinders cfg

vimBind :: (Show a, PrintfType t) => (SrcLoc.RealSrcSpan, ([Char], a)) -> t
vimBind (sp, (v, ann)) = printf "%d:%d-%d:%d::%s" l1 c1 l2 c2 (v ++ " :: " ++ show ann)
  where
    l1  = srcSpanStartLine sp
    c1  = srcSpanStartCol  sp
    l2  = srcSpanEndLine   sp
    c2  = srcSpanEndCol    sp

------------------------------------------------------------------------
-- | JSON Instances ----------------------------------------------------
------------------------------------------------------------------------

instance ToJSON ACSS.Status where
  toJSON ACSS.Safe   = "safe"
  toJSON ACSS.Unsafe = "unsafe"
  toJSON ACSS.Error  = "error"
  toJSON ACSS.Crash  = "crash"

instance ToJSON Annot1 where
  toJSON (A1 i a r c) = object [ "ident" .= i
                               , "ann"   .= a
                               , "row"   .= r
                               , "col"   .= c
                               ]

instance ToJSON Loc where
  toJSON (L (l, c)) = object [ "line"     .= toJSON l
                             , "column"   .= toJSON c ]

instance ToJSON AnnErrors where
  toJSON errs      = Array $ V.fromList $ fmap toJ errs
    where
      toJ (l,l',s) = object [ "start"   .= toJSON l
                            , "stop"    .= toJSON l'
                            , "message" .= toJSON s  ]

instance (Show k, ToJSON a) => ToJSON (Assoc k a) where
  toJSON (Asc kas) = object [ tshow k .= toJSON a | (k, a) <- M.toList kas ]
    where
      tshow        = T.pack . show

instance ToJSON ACSS.AnnMap where
  toJSON a = object [ "types"  .= toJSON (annTypes    a)
                    , "errors" .= toJSON (ACSS.errors a)
                    , "status" .= toJSON (ACSS.status a)
                    ]

annTypes         :: ACSS.AnnMap -> AnnTypes
annTypes a       = grp [(l, c, ann1 l c x s) | (l, c, x, s) <- binders]
  where
    ann1 l c x s = A1 x s l c
    grp          = L.foldl' (\m (r,c,x) -> ins r c x m) (Asc M.empty)
    binders      = [(l, c, x, s) | (L (l, c), (x, s)) <- M.toList $ ACSS.types a]

ins :: (Eq k, Eq k1, Hashable k, Hashable k1)
    => k -> k1 -> a -> Assoc k (Assoc k1 a) -> Assoc k (Assoc k1 a)
ins r c x (Asc m)  = Asc (M.insert r (Asc (M.insert c x rm)) m)
  where
    Asc rm         = M.lookupDefault (Asc M.empty) r m

--------------------------------------------------------------------------------
-- | LH Related Stuff ----------------------------------------------------------
--------------------------------------------------------------------------------

{-@ LIQUID "--diffcheck" @-}

{-@ type ListNE a    = {v:[a] | 0 < len v}  @-}
{-@ type ListN  a N  = {v:[a] | len v == N} @-}
{-@ type ListXs a Xs = ListN a {len Xs}     @-}

{-@ assume GHC.Exts.sortWith :: Ord b => (a -> b) -> xs:[a] -> ListXs a xs @-}
{-@ assume GHC.Exts.groupWith :: Ord b => (a -> b) -> [a] -> [ListNE a] @-}

--------------------------------------------------------------------------------
-- | A Little Unit Test --------------------------------------------------------
--------------------------------------------------------------------------------

_anns :: AnnTypes
_anns = i [(5,   i [( 14, A1 { ident = "foo"
                            , ann   = "int -> int"
                            , row   = 5
                            , col   = 14
                            })
                  ]
          )
         ,(9,   i [( 22, A1 { ident = "map"
                            , ann   = "(a -> b) -> [a] -> [b]"
                            , row   = 9
                            , col   = 22
                            })
                  ,( 28, A1 { ident = "xs"
                            , ann   = "[b]"
                            , row   = 9
                            , col   = 28
                            })
                  ])
         ]

i :: (Eq k, Hashable k) => [(k, a)] -> Assoc k a
i = Asc . M.fromList
