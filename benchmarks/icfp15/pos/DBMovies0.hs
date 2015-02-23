module MovieClient where
import DataBase hiding (D)

{-@ LIQUID "--real" @-}
import GHC.CString  -- This import interprets Strings as constants!

import Data.Maybe (catMaybes)

import qualified DataBase as DB

import Prelude hiding (product)

import Control.Applicative ((<$>))



movie1, movie2 :: MovieScheme
{-@ movie1, movie2 :: MovieScheme @-}
movie1 = ("title"    := S "Persepolis")
      += ("director" := S "Paronnaud") 
      += ("star"     := D 8) 
      += ("year"     := I 2007) 
      += empty

movie2 = ("title"    := S "Birdman") 
      += ("star"     := D 8.1) 
      += ("director" := S "Iñárritu")
      += ("year"     := I 2014) 
      += empty
         
movies :: Movies 
{-@ movies :: Movies @-}
movies = fromList [movie1, movie2]


{-@ tosee :: Titles @-}
goood_movies  =  select (
  \d -> toDouble (dfun d $ "star") > 8
  ) movies



type Tag = String 

data Value = I Int | S String | D Double
            deriving (Show, Eq)

data Name = ChickenPlums | TalkToHer | Persepolis | FunnyGames 
          | Paronnaud    | Almadovar | Haneke 
            deriving (Show, Eq)

{-@ type Movies      = [MovieScheme] @-}
{-@ type MovieScheme = {v:Dict <{\t val -> MovieRange t val}> Tag Value | ValidMovieScheme v} @-}
{-@ type Directors      = [DirectorScheme] @-}
{-@ type DirectorScheme = {v:Dict <{\t val -> DirectorRange t val}> Tag Value | ValidDirectorScheme v} @-}
{-@ type Stars      = [StarScheme] @-}
{-@ type StarScheme = {v:Dict <{\t val -> StarRange t val}> Tag Value | ValidStarScheme v} @-}
{-@ type Titles      = [TitleScheme] @-}
{-@ type TitleScheme = {v:Dict <{\t val -> TitleRange t val}> Tag Value | ValidTitleScheme v} @-}
{-@ type DirStars      = [DirStarScheme] @-}
{-@ type DirStarScheme = {v:Dict <{\t val -> DirStarRange t val}> Tag Value | ValidDirStarScheme v} @-}


{-@ predicate ValidMovieScheme V = 
	  ((listElts (ddom V) = Set_cup (Set_sng year) 
	  	                   (Set_cup (Set_sng star) 
	  	                   (Set_cup (Set_sng director) 
	  	                            (Set_sng title))))) @-}

{-@ predicate MovieRange  T V =    (T = year     => ValidYear     V) 
                                && (T = star     => ValidStar     V) 
                                && (T = director => ValidDirector V) 
                                && (T = title    => ValidTitle    V) @-}

{-@ predicate ValidDirectorScheme V = (listElts (ddom V) = (Set_sng director)) @-} 
{-@ predicate DirectorRange  T V = (T = director => ValidDirector V) @-}

{-@ predicate ValidStarScheme V = (listElts (ddom V) = (Set_sng star)) @-} 
{-@ predicate StarRange  T V    = (T = star => ValidStar V) @-}

{-@ predicate ValidTitleScheme V = (listElts (ddom V) = (Set_sng title)) @-} 
{-@ predicate TitleDomain T   = ( T = title) @-}
{-@ predicate TitleRange  T V = (T = title => ValidTitle V) @-}

{-@ predicate ValidDirStarScheme V = (listElts (ddom V) = Set_cup (Set_sng director) (Set_sng star)) @-} 
{-@ predicate DirStarDomain T   = ( T = director || T = star) @-}
{-@ predicate DirStarRange  T V = (T = director => ValidDirector V) && (T = star => ValidStar V)  @-}


{-@ predicate ValidYear     V = isInt V  && 1889 <= toInt V  @-}
{-@ predicate ValidStar     V = isDouble V  && 0.0 <= toDouble V && toDouble V <= 10.0 @-}
{-@ predicate ValidDirector V = isString V @-}
{-@ predicate ValidTitle    V = isString V @-}




type Movies    = Table Tag Value 
type Titles    = Table Tag Value 
type Directors = Table Tag Value
type Stars     = Table Tag Value
type DirStars  = Table Tag Value

type MovieScheme = Dict Tag Value



mkMovie :: Value -> Value -> Value -> Value -> MovieScheme
{-@ mkMovie :: {t:Value | ValidTitle t} 
            -> {d:Value | ValidDirector d}
            -> {s:Value | ValidStar s}
            -> {y:Value | ValidYear y}
            -> MovieScheme
  @-}          
mkMovie t d s y = ("title" := t) += ("star" := s) += ("director" := d) += ("year" := y) += empty

seen :: Titles
{-@ seen :: Titles @-}
seen = [t1, t2]
  where 
  	t1 = ("title" := S "ChickenPlums") += empty
  	t2 = ("title" := S "FunnyGames")   += empty

not_seen :: Movies
not_seen = select isSeen movies
  where
    isSeen (DB.D ks f) = not $ (f "title") `elem` (values "title" seen) 

{-@ not_seen, to_see :: Movies @-}
to_see = select isGoodMovie not_seen
  where
    isGoodMovie (DB.D ks f)  = (f "director") `elem` (values "director" good_directors)
                          && (toDouble (f "star")) >= 8.0

directors, good_directors :: Directors
{-@ directors, good_directors :: Directors @-}
directors = project ["director"] movies


good_stars :: Stars
{-@ good_stars :: Stars @-}
good_directors     = directors `diff` project ["director"] not_good_directors
-- This _IS_ unsafe!
-- good_directors     = directors `diff` not_good_directors

not_good_directors :: DirStars 
{-@ not_good_directors :: DirStars @-}
not_good_directors = project ["director", "star"] movies  `diff` product directors good_stars 

 
-- This _IS_ unsafe! 
-- not_good_directors = project ["director", "star"] movies  `diff` product directors movies

good_stars         = mk_star_table (D 8.0) `union` mk_star_table (D 9.0) `union` mk_star_table (D 10.0)  

mk_star_table :: Value -> Stars
{-@ mk_star_table :: {s:Value | ValidStar s} -> Stars @-}
mk_star_table s    = [("star" := s) += empty]


-------------------------------------------------------------------------------
--------------- Some measures -------------------------------------------------
-------------------------------------------------------------------------------


{-@ measure toInt :: Value -> Int 
    toInt(I n) = n
  @-}
{-@ measure toDouble :: Value -> Double 
    toDouble(D n) = n
  @-}

{-@ toInt :: {v:Value | isInt v} -> Int @-}
toInt :: Value -> Int
toInt (I n) = n

{-@ toDouble :: {v:Value | isDouble v} -> Double @-}
toDouble :: Value -> Double
toDouble (D n) = n

{-@ measure isInt @-}
isInt :: Value -> Bool
isInt (I _) = True
isInt _     = False

{-@ measure isDouble @-}
isDouble :: Value -> Bool
isDouble (D _) = True
isDouble _     = False

{-@ measure isString @-}
isString :: Value -> Bool
isString (S _) = True
isString _     = False
