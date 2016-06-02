-- | Formats Haskell source code as HTML with CSS and Mouseover Type Annotations
module Language.Haskell.HsColour.ACSS (
    hscolour
  , hsannot
  , AnnMap (..)
  , Loc (..)
  , breakS
  , srcModuleName 
  ) where

{-@ LIQUID "--totality"     @-}

import Language.Haskell.HsColour.General (liquidAssume)
import Language.Haskell.HsColour.Anchors
import Language.Haskell.HsColour.Classify as Classify
import Language.Haskell.HsColour.HTML (renderAnchors, renderComment,
                                       renderNewLinesAnchors, escape)
import qualified Language.Haskell.HsColour.CSS as CSS

import Data.Maybe  (fromMaybe) 
import qualified Data.Map as M
import Data.List   (isSuffixOf, findIndex, elemIndices, intercalate)
import Data.Char   (isLower, isSpace, isAlphaNum)
import Text.Printf
import Debug.Trace

newtype AnnMap = Ann (M.Map Loc (String, String))                    
newtype Loc    = L (Int, Int) deriving (Eq, Ord, Show)

-- | Formats Haskell source code using HTML and mouse-over annotations 
hscolour :: Bool     -- ^ Whether to include anchors.
         -> String   -- ^ Haskell source code, Annotations as comments at end
         -> String   -- ^ Coloured Haskell source code.

hscolour anchor = hsannot anchor . splitSrcAndAnns

-- | Formats Haskell source code using HTML and mouse-over annotations 
hsannot  :: Bool             -- ^ Whether to include anchors.
         -> (String, AnnMap) -- ^ Haskell Source, Annotations
         -> String           -- ^ Coloured Haskell source code.

hsannot anchor = 
    CSS.pre
    . (if anchor then -- renderNewLinesAnchors .
                      concatMap (renderAnchors renderAnnotToken)
                      . insertAnnotAnchors
                 else concatMap renderAnnotToken)
    . annotTokenise

annotTokenise  :: (String, AnnMap) -> [(TokenType, String, Maybe String)] 
annotTokenise (src, Ann annm) 
  = zipWith (\(x,y) z -> (x,y, snd `fmap` z)) toks annots 
  where toks       = tokenise src 
        spans      = tokenSpans $ map snd toks 
        annots     = map (`M.lookup` annm) spans

tokenSpans :: [String] -> [Loc]
tokenSpans = scanl plusLoc (L (1, 1)) 

plusLoc :: Loc -> String -> Loc
plusLoc (L (l, c)) s 
  = case '\n' `elemIndices` s of
      [] -> L (l, (c + n))
      is -> L ((l + length is), (n - maximum is))
    where n = length s

renderAnnotToken :: (TokenType, String, Maybe String) -> String
renderAnnotToken (x,y, Nothing) 
  = CSS.renderToken (x, y)
renderAnnotToken (x,y, Just ann)
  = printf template (escape ann) (CSS.renderToken (x, y))
    where template = "<a class=annot href=\"#\"><span class=annottext>%s</span>%s</a>"

{- Example Annotation:
<a class=annot href="#"><span class=annottext>x#agV:Int -&gt; {VV_int:Int | (0 &lt;= VV_int),(x#agV &lt;= VV_int)}</span>
<span class='hs-definition'>NOWTRYTHIS</span></a>
-}


insertAnnotAnchors :: [(TokenType, String, a)] -> [Either String (TokenType, String, a)]
insertAnnotAnchors toks 
  = stitch (zip toks' toks) $ insertAnchors toks'
  where toks' = [(x,y) | (x,y,_) <- toks] 

{-@ Decrease stitch 3 @-}

{-@ stitch ::  Eq b => xs:[(b, c)] -> {v:[Either a b] | (lenRight v) = (len xs)} -> [Either a c] @-}
stitch ::  Eq b => [(b, c)] -> [Either a b] -> [Either a c]
stitch xys ((Left a) : rest)
  = (Left a) : stitch xys rest
stitch ((x,y):xys) ((Right x'):rest) 
  | x == x' 
  = (Right y) : stitch xys rest
  | otherwise
  = error "stitch"
stitch _ []
  = []


splitSrcAndAnns ::  String -> (String, AnnMap) 
splitSrcAndAnns s = 
  let ls = lines s in
  case findIndex (breakS ==) ls of
    Nothing -> (s, Ann M.empty)
    Just i  -> (src, {- trace ("annm =" ++ show ann) -} ann)
               where (codes,xs)       = splitAt i ls
                     (_:mname:annots) = liquidAssume (length xs > 2) xs
                     ann   = annotParse mname $ dropWhile isSpace $ unlines annots
                     src   = unlines codes
                     -- mname = srcModuleName src

srcModuleName :: String -> String
srcModuleName = fromMaybe "Main" . tokenModule . tokenise
  
tokenModule toks 
  = do i <- findIndex ((Keyword, "module") ==) toks 
       let (_, toks')  = splitAt (i+2) toks
       j <- findIndex ((Space ==) . fst) toks'
       let (toks'', _) = splitAt j toks'
       return $ concatMap snd toks''

breakS = "MOUSEOVER ANNOTATIONS" 

annotParse :: String -> String -> AnnMap
annotParse mname = Ann . M.fromList . parseLines mname 0 . lines

{-@ Decrease parseLines 3 @-}

parseLines mname i [] 
  = []
parseLines mname i ("":ls)      
  = parseLines mname (i+1) ls
parseLines mname i (x:f:l:c:n:rest) 
  | f /= mname -- `isSuffixOf` mname 
  = {- trace ("wrong annot f = " ++ f ++ " mname = " ++ mname) $ -} parseLines mname (i + 5 + num) rest'
  | otherwise 
  = (L (line, col), (x, anns)) : parseLines mname (i + 5 + num) rest'
    where line  = (read l) :: Int
          col   = (read c) :: Int
          num   = (read n) :: Int
          anns  = intercalate "\n" $ take num rest
          rest' = drop num rest
parseLines _ i _              
  = error $ "Error Parsing Annot Input on Line: " ++ show i

takeFileName s = map slashWhite s
  where slashWhite '/' = ' '

instance Show AnnMap where
  show (Ann m) = "\n\n" ++ (concatMap ppAnnot $ M.toList m)
    where ppAnnot (L (l, c), (x,s)) =  x ++ "\n" 
                                    ++ show l ++ "\n"
                                    ++ show c ++ "\n"
                                    ++ show (length $ lines s) ++ "\n"
                                    ++ s ++ "\n\n\n"
