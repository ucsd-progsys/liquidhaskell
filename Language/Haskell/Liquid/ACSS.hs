-- | Formats Haskell source code as HTML with CSS and Mouseover Type Annotations
module Language.Haskell.Liquid.ACSS (
    hscolour
  , hsannot
  , Annotation (..)
  , AnnMap (..)
  , Loc (..)
  , breakS
  , srcModuleName 
  ) where

import Language.Haskell.HsColour.Anchors
import Language.Haskell.HsColour.Classify as Classify
import Language.Haskell.HsColour.HTML (renderAnchors, escape)
import qualified Language.Haskell.HsColour.CSS as CSS

import Data.Monoid
import Data.Maybe  (fromMaybe) 
import Data.Hashable
import qualified Data.HashMap.Strict as M
import Data.List   (foldl', isPrefixOf, findIndex, elemIndices, intercalate)
import Data.Char   (isSpace)
import Text.Printf
import Language.Haskell.Liquid.GhcMisc

-- import Debug.Trace

newtype AnnMap  = Ann (M.HashMap Loc (String, Annotation)) 

data Annotation = A { typ :: Maybe String
                    , err :: Maybe String 
                    } deriving (Eq, Show)

instance Monoid Annotation where
  mempty        = A Nothing Nothing
  mappend a1 a2 = A { typ = getFirstMaybe (typ a1) (typ a2)
                    , err = getFirstMaybe (err a1) (err a2) }

getFirstMaybe x@(Just _) _ = x
getFirstMaybe Nothing y    = y




-- | Formats Haskell source code using HTML and mouse-over annotations 
hscolour :: Bool     -- ^ Whether to include anchors.
         -> Bool     -- ^ Whether input document is literate haskell or not
         -> String   -- ^ Haskell source code, Annotations as comments at end
         -> String   -- ^ Coloured Haskell source code.

hscolour anchor lhs = hsannot anchor Nothing lhs . splitSrcAndAnns

type CommentTransform = Maybe (String -> [(TokenType, String)])

-- | Formats Haskell source code using HTML and mouse-over annotations 
hsannot  :: Bool             -- ^ Whether to include anchors.
         -> CommentTransform -- ^ Function to refine comment tokens 
         -> Bool             -- ^ Whether input document is literate haskell or not
         -> (String, AnnMap) -- ^ Haskell Source, Annotations
         -> String           -- ^ Coloured Haskell source code.

hsannot anchor tx False z     = hsannot' Nothing anchor tx z
hsannot anchor tx True (s, m) = concatMap chunk $ litSpans $ joinL $ classify $ inlines s
  where chunk (Code c, l)     = hsannot' (Just l) anchor tx (c, m)
        chunk (Lit c , _)     = c

litSpans :: [Lit] -> [(Lit, Loc)]
litSpans lits = zip lits $ spans lits
  where spans = tokenSpans Nothing . map unL

hsannot' baseLoc anchor tx = 
    CSS.pre
    . (if anchor then concatMap (renderAnchors renderAnnotToken)
                      . insertAnnotAnchors
                 else concatMap renderAnnotToken)
    . annotTokenise baseLoc tx

annotTokenise :: Maybe Loc -> CommentTransform -> (String, AnnMap) -> [(TokenType, String, Annotation)] 
annotTokenise baseLoc tx (src, Ann annm) 
  = zipWith (\(x,y) z -> (x,y,z)) toks annots 
  where toks       = tokeniseWithCommentTransform tx src 
        spans      = tokenSpans baseLoc $ map snd toks 
        annots     = map ((maybe mempty snd) . (`M.lookup` annm)) spans
                   -- map (\s -> snd $ M.lookup s annm) spans
                     

tokeniseWithCommentTransform :: Maybe (String -> [(TokenType, String)]) -> String -> [(TokenType, String)]
tokeniseWithCommentTransform Nothing  = tokenise
tokeniseWithCommentTransform (Just f) = concatMap (expand f) . tokenise
  where expand f (Comment, s) = f s
        expand _ z            = [z]

tokenSpans :: Maybe Loc -> [String] -> [Loc]
tokenSpans = scanl plusLoc . fromMaybe (L (1, 1)) 

plusLoc :: Loc -> String -> Loc
plusLoc (L (l, c)) s 
  = case '\n' `elemIndices` s of
      [] -> L (l, (c + n))
      is -> L ((l + length is), (n - maximum is))
    where n = length s

renderAnnotToken :: (TokenType, String, Annotation) -> String
renderAnnotToken (x, y, a)  = renderErrAnnot (err a) $ renderTypAnnot (typ a) $ CSS.renderToken (x, y)

renderErrAnnot (Just _) s   = printf "<a class=error href=\"#\">%s</a>" s 
renderErrAnnot Nothing  s   = s

renderTypAnnot (Just ann) s = printf "<a class=annot href=\"#\"><span class=annottext>%s</span>%s</a>" (escape ann) s
renderTypAnnot Nothing    s = s     


{- Example Annotation:
<a class=annot href="#"><span class=annottext>x#agV:Int -&gt; {VV_int:Int | (0 &lt;= VV_int),(x#agV &lt;= VV_int)}</span>
<span class='hs-definition'>NOWTRYTHIS</span></a>
-}


insertAnnotAnchors :: [(TokenType, String, a)] -> [Either String (TokenType, String, a)]
insertAnnotAnchors toks 
  = stitch (zip toks' toks) $ insertAnchors toks'
  where toks' = [(x,y) | (x,y,_) <- toks] 

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
               where (codes, _:mname:annots) = splitAt i ls
                     ann   = annotParse mname $ dropWhile isSpace $ unlines annots
                     src   = unlines codes

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
annotParse mname    = Ann . M.map reduce . group . parseLines mname 0 . lines
  where 
    group                 = foldl' (\m (k, v) -> inserts k v m) M.empty 
    reduce anns@((x,_):_) = (x, mconcat $ map snd anns)
    inserts k v m         = M.insert k (v : M.lookupDefault [] k m) m

parseLines _ _ [] 
  = []
parseLines mname i ("":ls)      
  = parseLines mname (i+1) ls
parseLines mname i (x:f:l:c:n:rest) 
  | f /= mname
  = parseLines mname (i + 5 + num) rest'
  | otherwise 
  = (L (line, col), (x, anns)) : parseLines mname (i + 5 + num) rest'
    where line  = (read l) :: Int
          col   = (read c) :: Int
          num   = (read n) :: Int
          anns  = stringAnnotation $ intercalate "\n" $ take num rest
          rest' = drop num rest
parseLines _ i _              
  = error $ "Error Parsing Annot Input on Line: " ++ show i

stringAnnotation s 
  | "ERROR" `isPrefixOf` s = A Nothing (Just s)
  | otherwise              = A (Just s) Nothing

-- takeFileName s = map slashWhite s
--   where slashWhite '/' = ' '

instance Show AnnMap where
  show (Ann m) = "\n\n" ++ (concatMap ppAnnot $ M.toList m)
    where 
      ppAnnot (L (l, c), (x, a)) = maybe "" (showId x l c) (typ a) ++ 
                                   maybe "" (showId x l c) (err a) 
      showId x l c s             = printf "%s\n%d\n%d\n%d\n%s\n\n\n" x l c (length $ lines s) s 

--     where ppAnnot (L (l, c), (x,s)) =  x ++ "\n" 
--                                     ++ show l ++ "\n"
--                                     ++ show c ++ "\n"
--                                     ++ show (length $ lines s) ++ "\n"
--                                     ++ s ++ "\n\n\n"


---------------------------------------------------------------------------------
---- Code for Dealing With LHS, stolen from Language.Haskell.HsColour.HsColour --
---------------------------------------------------------------------------------

-- | Separating literate files into code\/comment chunks.
data Lit = Code {unL :: String} | Lit {unL :: String} deriving (Show)

-- Re-implementation of 'lines', for better efficiency (but decreased laziness).
-- Also, importantly, accepts non-standard DOS and Mac line ending characters.
-- And retains the trailing '\n' character in each resultant string.
inlines :: String -> [String]
inlines s = lines' s id
  where
  lines' []             acc = [acc []]
  lines' ('\^M':'\n':s) acc = acc ['\n'] : lines' s id	-- DOS
--lines' ('\^M':s)      acc = acc ['\n'] : lines' s id	-- MacOS
  lines' ('\n':s)       acc = acc ['\n'] : lines' s id	-- Unix
  lines' (c:s)          acc = lines' s (acc . (c:))


-- | The code for classify is largely stolen from Language.Preprocessor.Unlit.
classify ::  [String] -> [Lit]
classify []             = []
classify (x:xs) | "\\begin{code}"`isPrefixOf`x
                        = Lit x: allProg xs
   where allProg []     = []  -- Should give an error message,
                              -- but I have no good position information.
         allProg (x:xs) | "\\end{code}"`isPrefixOf`x
                        = Lit x: classify xs
         allProg (x:xs) = Code x: allProg xs
classify (('>':x):xs)   = Code ('>':x) : classify xs
classify (x:xs)         = Lit x: classify xs

-- | Join up chunks of code\/comment that are next to each other.
joinL :: [Lit] -> [Lit]
joinL []                  = []
joinL (Code c:Code c2:xs) = joinL (Code (c++c2):xs)
joinL (Lit c :Lit c2 :xs) = joinL (Lit  (c++c2):xs)
joinL (any:xs)            = any: joinL xs

