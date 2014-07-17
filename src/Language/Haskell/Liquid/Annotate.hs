{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}

---------------------------------------------------------------------------
-- | This module contains the code that uses the inferred types to generate 
-- 1. HTMLized source with Inferred Types in mouseover annotations.
-- 2. Annotations files (e.g. for vim/emacs)
-- 3. JSON files for the web-demo etc.
---------------------------------------------------------------------------

module Language.Haskell.Liquid.Annotate (mkOutput, annotate) where

import           GHC                      ( SrcSpan (..)
                                          , srcSpanStartCol
                                          , srcSpanEndCol
                                          , srcSpanStartLine
                                          , srcSpanEndLine
                                          , RealSrcSpan (..))
import           Var                      (Var (..))
import           TypeRep                  (Prec(..))
import           Text.PrettyPrint.HughesPJ hiding (first, second)
import           GHC.Exts                 (groupWith, sortWith)

import           Data.Char                (isSpace)
import           Data.Function            (on)
import           Data.List                (sortBy)
import           Data.Maybe               (mapMaybe)

import           Data.Aeson               
import           Control.Arrow            hiding ((<+>))
import           Control.Applicative      ((<$>))
import           Control.DeepSeq
import           Control.Monad            (when, forM_)
import           Data.Monoid

import           System.FilePath          (takeFileName, dropFileName, (</>)) 
import           System.Directory         (findExecutable, copyFile)
import           Text.Printf              (printf)
import qualified Data.List              as L
import qualified Data.Vector            as V
import qualified Data.ByteString.Lazy   as B
import qualified Data.Text              as T
import qualified Data.HashMap.Strict    as M
import qualified Language.Haskell.Liquid.ACSS as ACSS
import           Language.Haskell.HsColour.Classify
import           Language.Fixpoint.Files
import           Language.Fixpoint.Names
import           Language.Fixpoint.Misc
import           Language.Haskell.Liquid.GhcMisc
import           Language.Fixpoint.Types hiding (Def (..), Located (..))
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.PrettyPrint
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Errors
import           Language.Haskell.Liquid.Tidy
import           Language.Haskell.Liquid.Types hiding (Located(..), Def(..))

-- | @output@ creates the pretty printed output
--------------------------------------------------------------------------------------------
mkOutput :: Config -> FixResult Error -> FixSolution -> AnnInfo (Annot SpecType) -> Output Doc
--------------------------------------------------------------------------------------------
mkOutput cfg res sol anna 
  = O { o_vars   = Nothing
      , o_warns  = []
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
annotate :: Config -> FilePath -> Output Doc -> IO () 
-------------------------------------------------------------------
annotate cfg srcF out
  = do generateHtml srcF tpHtmlF tplAnnMap
       generateHtml srcF tyHtmlF typAnnMap 
       writeFile         vimF  $ vimAnnot cfg annTyp 
       B.writeFile       jsonF $ encode typAnnMap
       forM_ bots (printf "WARNING: Found false in %s\n" . showPpr)
    where
       tplAnnMap  = mkAnnMap cfg result annTpl
       typAnnMap  = mkAnnMap cfg result annTyp
       annTpl     = o_templs out
       annTyp     = o_types  out
       result     = o_result out
       bots       = o_bots   out
       tyHtmlF    = extFileName Html                   srcF  
       tpHtmlF    = extFileName Html $ extFileName Cst srcF 
       annF       = extFileName Annot srcF
       jsonF      = extFileName Json  srcF  
       vimF       = extFileName Vim   srcF

mkBots (AI m) = [ src | (src, (Just _, t) : _) <- sortBy (compare `on` fst) $ M.toList m
                      , isFalse (rTypeReft t) ]

writeFilesOrStrings :: FilePath -> [Either FilePath String] -> IO ()
writeFilesOrStrings tgtFile = mapM_ $ either (`copyFile` tgtFile) (tgtFile `appendFile`) 

generateHtml srcF htmlF annm
  = do src     <- readFile srcF
       let lhs  = isExtFile LHs srcF
       let body = {-# SCC "hsannot" #-} ACSS.hsannot False (Just tokAnnot) lhs (src, annm)
       cssFile <- getCssPath
       copyFile cssFile (dropFileName htmlF </> takeFileName cssFile) 
       renderHtml lhs htmlF srcF (takeFileName cssFile) body

renderHtml True  = renderPandoc 
renderHtml False = renderDirect

-------------------------------------------------------------------------
-- | Pandoc HTML Rendering (for lhs + markdown source) ------------------ 
-------------------------------------------------------------------------
     
renderPandoc htmlFile srcFile css body
  = do renderFn <- maybe renderDirect renderPandoc' <$> findExecutable "pandoc"  
       renderFn htmlFile srcFile css body

renderPandoc' pandocPath htmlFile srcFile css body
  = do _  <- writeFile mdFile $ pandocPreProc body
       ec <- executeShellCommand "pandoc" cmd 
       writeFilesOrStrings htmlFile [Right (cssHTML css)]
       checkExitCode cmd ec
    where mdFile = extFileName Mkdn srcFile 
          cmd    = pandocCmd pandocPath mdFile htmlFile

pandocCmd pandocPath mdFile htmlFile
  = printf "%s -f markdown -t html %s > %s" pandocPath mdFile htmlFile  

pandocPreProc  = T.unpack . stripBegin . stripEnd . T.pack
  where 
    stripBegin = T.replace (T.pack "\\begin{code}") T.empty 
    stripEnd   = T.replace (T.pack "\\end{code}")   T.empty 

-------------------------------------------------------------------------
-- | Direct HTML Rendering (for non-lhs/markdown source) ---------------- 
-------------------------------------------------------------------------

-- More or less taken from hscolour

renderDirect htmlFile srcFile css body 
  = writeFile htmlFile $! (top'n'tail full srcFile css $! body)
    where full = True -- False  -- TODO: command-line-option 

-- | @top'n'tail True@ is used for standalone HTML, 
--   @top'n'tail False@ for embedded HTML

top'n'tail True  title css = (htmlHeader title css ++) . (++ htmlClose)
top'n'tail False _    _    = id

-- Use this for standalone HTML

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

htmlClose  = "\n</body>\n</html>"

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

mkAnnMap :: Config -> FixResult Error -> AnnInfo Doc -> ACSS.AnnMap
mkAnnMap cfg res ann     = ACSS.Ann (mkAnnMapTyp cfg ann) (mkAnnMapErr res) (mkStatus res)

mkStatus (Safe)          = ACSS.Safe
mkStatus (Unsafe _)      = ACSS.Unsafe
mkStatus (Crash _ _)     = ACSS.Error
mkStatus _               = ACSS.Crash

mkAnnMapErr (Unsafe ls)  = mapMaybe cinfoErr ls
mkAnnMapErr (Crash ls _) = mapMaybe cinfoErr ls 
mkAnnMapErr _            = []
 
cinfoErr e = case pos e of
               RealSrcSpan l -> Just (srcSpanStartLoc l, srcSpanEndLoc l, showpp e)
               _             -> Nothing

-- cinfoErr (Ci (RealSrcSpan l) e) = 
-- cinfoErr _                      = Nothing


-- mkAnnMapTyp :: (RefTypable a c tv r, RefTypable a c tv (), PPrint tv, PPrint a) =>Config-> AnnInfo (RType a c tv r) -> M.HashMap Loc (String, String)
mkAnnMapTyp cfg z = M.fromList $ map (first srcSpanStartLoc) $ mkAnnMapBinders cfg z

mkAnnMapBinders cfg (AI m)
  = map (second bindStr . head . sortWith (srcSpanEndCol . fst))
  $ groupWith (lineCol . fst)
    [ (l, x) | (RealSrcSpan l, x:_) <- M.toList m, oneLine l]
  where
    bindStr (x, v) = (maybe "_" shorten x, render v)
    shorten        = if shortNames cfg then dropModuleNames else id

closeAnnots :: AnnInfo (Annot SpecType) -> AnnInfo SpecType 
closeAnnots = closeA . filterA . collapseA

closeA a@(AI m)   = cf <$> a 
  where 
    cf (AnnLoc l)  = case m `mlookup` l of
                      [(_, AnnUse t)] -> t
                      [(_, AnnDef t)] -> t
                      [(_, AnnRDf t)] -> t
                      _               -> errorstar $ "malformed AnnInfo: " ++ showPpr l
    cf (AnnUse t) = t
    cf (AnnDef t) = t
    cf (AnnRDf t) = t

filterA (AI m) = AI (M.filter ff m)
  where 
    ff [(_, AnnLoc l)] = l `M.member` m
    ff _               = True

collapseA (AI m) = AI (fmap pickOneA m)

pickOneA xas = case (rs, ds, ls, us) of
                 (x:_, _, _, _) -> [x]
                 (_, x:_, _, _) -> [x]
                 (_, _, x:_, _) -> [x]
                 (_, _, _, x:_) -> [x]
  where 
    rs = [x | x@(_, AnnRDf _) <- xas]
    ds = [x | x@(_, AnnDef _) <- xas]
    ls = [x | x@(_, AnnLoc _) <- xas]
    us = [x | x@(_, AnnUse _) <- xas]

------------------------------------------------------------------------------
-- | Tokenizing Refinement Type Annotations in @-blocks ----------------------
------------------------------------------------------------------------------

-- | The token used for refinement symbols inside the highlighted types in @-blocks.
refToken = Keyword

-- | The top-level function for tokenizing @-block annotations. Used to
-- tokenize comments by ACSS.
tokAnnot s 
  = case trimLiquidAnnot s of 
      Just (l, body, r) -> [(refToken, l)] ++ tokBody body ++ [(refToken, r)]
      Nothing           -> [(Comment, s)]

trimLiquidAnnot ('{':'-':'@':ss) 
  | drop (length ss - 3) ss == "@-}"
  = Just ("{-@", take (length ss - 3) ss, "@-}") 
trimLiquidAnnot _  
  = Nothing

tokBody s 
  | isData s  = tokenise s
  | isType s  = tokenise s
  | isIncl s  = tokenise s
  | isMeas s  = tokenise s
  | otherwise = tokeniseSpec s 

isMeas = spacePrefix "measure"
isData = spacePrefix "data"
isType = spacePrefix "type"
isIncl = spacePrefix "include"

spacePrefix str s@(c:cs)
  | isSpace c   = spacePrefix str cs
  | otherwise   = take (length str) s == str
spacePrefix _ _ = False 


tokeniseSpec       ::  String -> [(TokenType, String)]
tokeniseSpec str   = {- traceShow ("tokeniseSpec: " ++ str) $ -} tokeniseSpec' str

tokeniseSpec'      = tokAlt . chopAltDBG -- [('{', ':'), ('|', '}')] 
  where 
    tokAlt (s:ss)  = tokenise s ++ tokAlt' ss
    tokAlt _       = []
    tokAlt' (s:ss) = (refToken, s) : tokAlt ss
    tokAlt' _      = []

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

ins r c x (Asc m)  = Asc (M.insert r (Asc (M.insert c x rm)) m)
  where 
    Asc rm         = M.lookupDefault (Asc M.empty) r m



--------------------------------------------------------------------------------
-- | A Little Unit Test --------------------------------------------------------
--------------------------------------------------------------------------------

anns :: AnnTypes  
anns = i [(5,   i [( 14, A1 { ident = "foo"
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
 
i = Asc . M.fromList



