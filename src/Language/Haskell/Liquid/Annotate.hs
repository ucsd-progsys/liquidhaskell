{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}

-- | This module contains the code that uses the inferred types to generate
-- htmlized source with mouseover annotations.

module Language.Haskell.Liquid.Annotate (
  
  -- * Types representing annotations
    AnnInfo (..)
  , Annot (..)

  -- * Top-level annotation renderer function
  , annotate
  ) where

import GHC                      ( SrcSpan (..)
                                , srcSpanStartCol
                                , srcSpanEndCol
                                , srcSpanStartLine
                                , srcSpanEndLine)

import Var                      (Var (..))                                
import Text.PrettyPrint.HughesPJ
import GHC.Exts                 (groupWith, sortWith)

import Data.Char                (isSpace)
import Data.Function            (on)
import Data.List                (sortBy)
import Data.Maybe               (mapMaybe)

import Data.Aeson               
import Control.Arrow            hiding ((<+>))
import Control.Applicative      ((<$>))
import Control.DeepSeq
import Control.Monad            (when)
import Data.Monoid

import System.FilePath          (takeFileName, dropFileName, (</>)) 
import System.Directory         (findExecutable, copyFile)
import Text.Printf              (printf)

import qualified Data.ByteString.Lazy   as B
import qualified Data.Text              as T
import qualified Data.HashMap.Strict    as M

import qualified Language.Haskell.Liquid.ACSS as ACSS

import Language.Haskell.HsColour.Classify
import Language.Fixpoint.Files
import Language.Fixpoint.Names
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.GhcMisc
import Language.Fixpoint.Types hiding (Def (..))
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.Tidy
import Language.Haskell.Liquid.Types hiding (Located(..), Def(..))
-- import Language.Haskell.Liquid.Result

import qualified Data.List           as L
import qualified Data.Vector         as V

-- import           Language.Fixpoint.Misc (inserts)
-- import           Language.Haskell.Liquid.ACSS


-------------------------------------------------------------------
------ Rendering HTMLized source with Inferred Types --------------
-------------------------------------------------------------------

annotate :: FilePath -> FixResult Error -> FixSolution -> AnnInfo Annot -> IO ()
annotate fname result sol anna 
  = do annotDump fname (extFileName Html $ extFileName Cst fname) result annm
       annotDump fname (extFileName Html fname) result annm'
       showBots annm'
    where
      annm  = closeAnnots anna
      annm' = tidySpecType <$> applySolution sol annm

showBots (AI m) = mapM_ showBot $ sortBy (compare `on` fst) $ M.toList m
  where
    showBot (src, (Just v, spec):_) =
        when (isFalse (rTypeReft spec)) $
             printf "WARNING: Found false in %s\n" (showPpr src)
    showBot _ = return ()

annotDump :: FilePath -> FilePath -> FixResult Error -> AnnInfo SpecType -> IO ()
annotDump srcFile htmlFile result ann
  = do let annm     = mkAnnMap result ann
       let annFile  = extFileName Annot srcFile
       let jsonFile = extFileName Json  srcFile  
       B.writeFile           jsonFile (encode annm) 
       writeFilesOrStrings   annFile  [Left srcFile, Right (show annm)]
       annotHtmlDump         htmlFile srcFile annm 
       return ()

writeFilesOrStrings :: FilePath -> [Either FilePath String] -> IO ()
writeFilesOrStrings tgtFile = mapM_ $ either (`copyFile` tgtFile) (tgtFile `appendFile`) 

annotHtmlDump htmlFile srcFile annm
  = do src     <- readFile srcFile
       let lhs  = isExtFile LHs srcFile
       let body = {-# SCC "hsannot" #-} ACSS.hsannot False (Just tokAnnot) lhs (src, annm)
       cssFile <- getCssPath
       copyFile cssFile (dropFileName htmlFile </> takeFileName cssFile) 
       renderHtml lhs htmlFile srcFile (takeFileName cssFile) body

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

mkAnnMap ::  FixResult Error -> AnnInfo SpecType -> ACSS.AnnMap
mkAnnMap res ann = ACSS.Ann (mkAnnMapTyp ann) (mkAnnMapErr res) (mkStatus res)

mkStatus (Safe)      = ACSS.Safe
mkStatus (Unsafe _)  = ACSS.Unsafe
mkStatus (Crash _ _) = ACSS.Error
mkStatus _           = ACSS.Crash

mkAnnMapErr (Unsafe ls)  = mapMaybe cinfoErr ls
mkAnnMapErr (Crash ls _) = mapMaybe cinfoErr ls 
mkAnnMapErr _            = []
 
cinfoErr e = case pos e of
               RealSrcSpan l -> Just (srcSpanStartLoc l, srcSpanEndLoc l, showpp e)
               _             -> Nothing

-- cinfoErr (Ci (RealSrcSpan l) e) = 
-- cinfoErr _                      = Nothing


mkAnnMapTyp (AI m) = M.fromList
                     $ map (srcSpanStartLoc *** bindString)
                     $ map (head . sortWith (srcSpanEndCol . fst)) 
                     $ groupWith (lineCol . fst) 
                     $ [ (l, x) | (RealSrcSpan l, (x:_)) <- M.toList m, oneLine l]  
  where 
    bindString     = mapPair render . pprXOT 

closeAnnots :: AnnInfo Annot -> AnnInfo SpecType 
closeAnnots = closeA . filterA . collapseA

closeA a@(AI m)  = cf <$> a 
  where 
    cf (Loc loc) = case m `mlookup` loc of
                         [(_, Use t)] -> t
                         [(_, Def t)] -> t
                         [(_, RDf t)] -> t
                         _            -> errorstar $ "malformed AnnInfo: " ++ showPpr loc
    cf (Use t)        = t
    cf (Def t)        = t
    cf (RDf t)        = t

filterA (AI m) = AI (M.filter ff m)
  where ff [(_, Loc loc)] = loc `M.member` m
        ff _              = True

collapseA (AI m) = AI (fmap pickOneA m)

pickOneA xas = case (rs, ds, ls, us) of
                 ((x:_), _, _, _) -> [x]
                 (_, (x:_), _, _) -> [x]
                 (_, _, (x:_), _) -> [x]
                 (_, _, _, (x:_)) -> [x]
  where 
    rs = [x | x@(_, RDf _) <- xas]
    ds = [x | x@(_, Def _) <- xas]
    ls = [x | x@(_, Loc _) <- xas]
    us = [x | x@(_, Use _) <- xas]

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
  | otherwise   = (take (length str) s) == str
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

---------------------------------------------------------------
---------------- Annotations and Solutions --------------------
---------------------------------------------------------------

newtype AnnInfo a = AI (M.HashMap SrcSpan [(Maybe Var, a)])

data Annot        = Use SpecType 
                  | Def SpecType 
                  | RDf SpecType
                  | Loc SrcSpan

instance Monoid (AnnInfo a) where
  mempty                  = AI M.empty
  mappend (AI m1) (AI m2) = AI $ M.unionWith (++) m1 m2

instance Functor AnnInfo where
  fmap f (AI m) = AI (fmap (fmap (\(x, y) -> (x, f y))) m)

instance PPrint a => PPrint (AnnInfo a) where
  pprint (AI m) = vcat $ map pprAnnInfoBinds $ M.toList m 


instance NFData a => NFData (AnnInfo a) where
  rnf (AI x) = () -- rnf x

instance NFData Annot where
  rnf (Def x) = () -- rnf x
  rnf (RDf x) = () -- rnf x
  rnf (Use x) = () -- rnf x
  rnf (Loc x) = () -- rnf x

instance PPrint Annot where
  pprint (Use t) = text "Use" <+> pprint t
  pprint (Def t) = text "Def" <+> pprint t
  pprint (RDf t) = text "RDf" <+> pprint t
  pprint (Loc l) = text "Loc" <+> pprDoc l

pprAnnInfoBinds (l, xvs) 
  = vcat $ map (pprAnnInfoBind . (l,)) xvs

pprAnnInfoBind (RealSrcSpan k, xv) 
  = xd $$ pprDoc l $$ pprDoc c $$ pprint n $$ vd $$ text "\n\n\n"
    where l        = srcSpanStartLine k
          c        = srcSpanStartCol k
          (xd, vd) = pprXOT xv 
          n        = length $ lines $ render vd

pprAnnInfoBind (_, _) 
  = empty

pprXOT (x, v) = (xd, pprint v)
  where xd = maybe (text "unknown") pprint x

applySolution :: FixSolution -> AnnInfo SpecType -> AnnInfo SpecType 
applySolution = fmap . fmap . mapReft . map . appSolRefa 
  where appSolRefa _ ra@(RConc _) = ra 
        -- appSolRefa _ p@(RPvar _)  = p  
        appSolRefa s (RKvar k su) = RConc $ subst su $ M.lookupDefault PTop k s  
        mapReft f (U (Reft (x, zs)) p) = U (Reft (x, squishRefas $ f zs)) p



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
  toJSON (L (l, c)) = object [ ("line"     .= toJSON l)
                             , ("column"   .= toJSON c) ]

instance ToJSON AnnErrors where 
  toJSON errs      = Array $ V.fromList $ fmap toJ errs
    where 
      toJ (l,l',s) = object [ ("start"   .= toJSON l )
                            , ("stop"    .= toJSON l') 
                            , ("message" .= toJSON s ) ]

instance (Show k, ToJSON a) => ToJSON (Assoc k a) where
  toJSON (Asc kas) = object [ (tshow k) .= (toJSON a) | (k, a) <- M.toList kas ]
    where
      tshow        = T.pack . show 

instance ToJSON ACSS.AnnMap where 
  toJSON a = object [ ("types"  .= (toJSON $ annTypes a))
                    , ("errors" .= (toJSON $ ACSS.errors   a))
                    , ("status" .= (toJSON $ ACSS.status   a))
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



