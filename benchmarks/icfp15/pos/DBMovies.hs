module MovieClient where
import DataBase

import GHC.CString  -- This import interprets Strings as constants!

import Data.Maybe (catMaybes)

import Prelude hiding (product, elem)

import Control.Applicative ((<$>))


type Tag = String

data Value = I Int | S Name
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
	  ((listElts (ddom V) ~~ Set_cup (Set_sng "year")
	  	                     (Set_cup (Set_sng "star")
	  	                     (Set_cup (Set_sng "director")
	  	                              (Set_sng "title"))))) @-}



{-@ predicate MovieRange  T V =    (T ~~ "year"     => ValidYear     V)
                                && (T ~~ "star"     => ValidStar     V)
                                && (T ~~ "director" => ValidDirector V)
                                && (T ~~ "title"    => ValidTitle    V)
                                @-}



{-@ predicate ValidDirectorScheme V = (listElts (ddom V) ~~ (Set_sng "director")) @-}
{-@ predicate DirectorRange  T V = (T ~~ "director" => ValidDirector V) @-}

{-@ predicate ValidStarScheme V = (listElts (ddom V) ~~ (Set_sng "star")) @-}
{-@ predicate StarRange  T V    = (T ~~ "star" => ValidStar V) @-}

{-@ predicate ValidTitleScheme V = (listElts (ddom V) ~~ (Set_sng "title")) @-}
{-@ predicate TitleDomain T   = (T ~~ "title") @-}
{-@ predicate TitleRange  T V = (T ~~ "title" => ValidTitle V) @-}

{-@ predicate ValidDirStarScheme V = (listElts (ddom V) ~~ Set_cup (Set_sng "director") (Set_sng "star")) @-}
{-@ predicate DirStarDomain T   = (T ~~ "director" || T ~~ "star") @-}
{-@ predicate DirStarRange  T V = (T ~~ "director" => ValidDirector V) && (T ~~ "star" => ValidStar V)  @-}


{-@ predicate ValidYear     V = isInt V  && 1889 <= toInt V  @-}
{-@ predicate ValidStar     V = isInt V  && 0 <= toInt V && toInt V <= 10 @-}
{-@ predicate ValidDirector V = isString V @-}
{-@ predicate ValidTitle    V = isString V @-}




type Movies    = Table Tag Value
type Titles    = Table Tag Value
type Directors = Table Tag Value
type Stars     = Table Tag Value
type DirStars  = Table Tag Value

type MovieScheme = Dict Tag Value

movies :: Movies
{-@ movies :: Movies @-}
movies = fromList [movie1, movie2, movie3, movie4]

movie1, movie2, movie3, movie4 :: MovieScheme
{-@ movie1, movie2, movie3, movie4 :: MovieScheme @-}
movie1 = mkMovie (S TalkToHer)    (S Almadovar) (I 8) (I 2002)
movie2 = mkMovie (S ChickenPlums) (S Paronnaud) (I 7) (I 2011)
movie3 = mkMovie (S Persepolis)   (S Paronnaud) (I 8) (I 2007)
movie4 = mkMovie (S FunnyGames)   (S Haneke)    (I 7) (I 2007)

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
  	t1 = ("title" := S ChickenPlums) += empty
  	t2 = ("title" := S FunnyGames)   += empty

not_seen :: Movies
not_seen = select isSeen movies
  where
    {-@ isSeen :: MovieScheme -> Bool @-}
    isSeen (D ks f) = not $ (f "title") `elem` (values "title" seen)

{-@ not_seen, to_see :: Movies @-}
to_see = select isGoodMovie not_seen
  where
    {-@ isGoodMovie :: MovieScheme -> Bool @-}
    isGoodMovie (D ks f)  = (f "director") `elem` (values "director" good_directors)
                          && (toInt (f "star")) >= 8

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

good_stars         = mk_star_table (I 8) `union` mk_star_table (I 9) `union` mk_star_table (I 10)

mk_star_table :: Value -> Stars
{-@ mk_star_table :: {s:Value | ValidStar s} -> Stars @-}
mk_star_table s    = [("star" := s) += empty]


-------------------------------------------------------------------------------
--------------- Some measures -------------------------------------------------
-------------------------------------------------------------------------------


{-@ measure toInt :: Value -> Int
    toInt(I n) = n
  @-}

{-@ toInt :: {v:Value | isInt v} -> Int @-}
toInt :: Value -> Int
toInt (I n) = n

{-@ measure isInt @-}
isInt :: Value -> Bool
isInt (I _) = True
isInt _     = False

{-@ measure isString @-}
isString :: Value -> Bool
isString (S _) = True
isString _     = False
