module MovieClient where
import DataBase


import Data.Maybe (catMaybes)

import Prelude hiding (product)

import Control.Applicative ((<$>))

data Tag   = Title | Director | Star | Year 
            deriving (Show, Eq)

data Value = I Int | S Name  
            deriving (Show, Eq)

data Name = ChickenPlums | TalkToHer | Persepolis | FunnyGames 
          | Paronnaud    | Almadovar | Haneke 
            deriving (Show, Eq)

{-@ type Movies      = [MovieScheme] @-}
{-@ type MovieScheme = {v:Dict <{\t -> MovieDomain t}, {\t val -> MovieRange t val}> Tag Value | ValidMovieScheme v} @-}
{-@ type Directors      = [DirectorScheme] @-}
{-@ type DirectorScheme = {v:Dict <{\t -> DirectorDomain t}, {\t val -> DirectorRange t val}> Tag Value | ValidDirectorScheme v} @-}
{-@ type Stars      = [StarScheme] @-}
{-@ type StarScheme = {v:Dict <{\t -> StarDomain t}, {\t val -> StarRange t val}> Tag Value | ValidStarScheme v} @-}
{-@ type Titles      = [TitleScheme] @-}
{-@ type TitleScheme = {v:Dict <{\t -> TitleDomain t}, {\t val -> TitleRange t val}> Tag Value | ValidTitleScheme v} @-}
{-@ type DirStars      = [DirStarScheme] @-}
{-@ type DirStarScheme = {v:Dict <{\t -> DirStarDomain t}, {\t val -> DirStarRange t val}> Tag Value | ValidDirStarScheme v} @-}


{-@ predicate ValidMovieScheme V = 
	  ((listElts (ddom V) = Set_cup (Set_sng Year) 
	  	                   (Set_cup (Set_sng Star) 
	  	                   (Set_cup (Set_sng Director) 
	  	                            (Set_sng Title))))) @-}

{-@ predicate MovieDomain T   = (T = Year || T = Star || T = Director || T = Title) @-}

{-@ predicate MovieRange  T V =    (T = Year     => ValidYear     V) 
                                && (T = Star     => ValidStar     V) 
                                && (T = Director => ValidDirector V) 
                                && (T = Title    => ValidTitle    V) @-}

{-@ predicate ValidDirectorScheme V = (listElts (ddom V) = (Set_sng Director)) @-} 
{-@ predicate DirectorDomain T   = ( T = Director ) @-}
{-@ predicate DirectorRange  T V = (T = Director => ValidDirector V) @-}

{-@ predicate ValidStarScheme V = (listElts (ddom V) = (Set_sng Star)) @-} 
{-@ predicate StarDomain T      = (T = Star) @-}
{-@ predicate StarRange  T V    = (T = Star => ValidStar V) @-}

{-@ predicate ValidTitleScheme V = (listElts (ddom V) = (Set_sng Title)) @-} 
{-@ predicate TitleDomain T   = ( T = Title) @-}
{-@ predicate TitleRange  T V = (T = Title => ValidTitle V) @-}

{-@ predicate ValidDirStarScheme V = (listElts (ddom V) = Set_cup (Set_sng Director) (Set_sng Star)) @-} 
{-@ predicate DirStarDomain T   = ( T = Director || T = Star) @-}
{-@ predicate DirStarRange  T V = (T = Director => ValidDirector V) && (T = Star => ValidStar V)  @-}


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
mkMovie t d s y = (Title := t) += (Star := s) += (Director := d) += (Year := y) += empty

seen :: Titles
{-@ seen :: Titles @-}
seen = [t1, t2]
  where 
  	t1 = (Title := S ChickenPlums) += empty
  	t2 = (Title := S FunnyGames)   += empty

not_seen :: Movies
not_seen = select isSeen movies
  where
  	isSeen Title t = not $ t `elem` (values Title seen)
  	isSeen _     _ = True

to_see = select isGoodMovie not_seen
  where
   isGoodMovie Star     (I s) = s >= 8
   isGoodMovie Director d     = d `elem` (values Director good_directors)
   isGoodMovie _        _     = True

directors, good_directors :: Directors
{-@ directors, good_directors :: Directors @-}
directors = project [Director] movies


good_stars :: Stars
{-@ good_stars :: Stars @-}
good_directors     = directors `diff` project [Director] not_good_directors
-- This _IS_ unsafe!
-- good_directors     = directors `diff` not_good_directors

not_good_directors :: DirStars 
{-@ not_good_directors :: DirStars @-}
not_good_directors = project [Director, Star] movies  `diff` [ productD x y | x <- directors, y <- good_stars] 

-- This _IS_ unsafe! 
-- not_good_directors = project [Director, Star] movies  `diff` [ productD x y | x <- directors, y <- movies] 

good_stars         = mk_star_table (I 8) `union` mk_star_table (I 9) `union` mk_star_table (I 10)  

mk_star_table :: Value -> Stars
{-@ mk_star_table :: {s:Value | ValidStar s} -> Stars @-}
mk_star_table s    = [(Star := s) += empty]


-------------------------------------------------------------------------------
--------------- Some measures -------------------------------------------------
-------------------------------------------------------------------------------


{-@ measure toInt :: Value -> Int 
    toInt(I n) = n
  @-}

{-@ measure isInt @-}
isInt :: Value -> Bool
isInt (I _) = True
isInt _     = False

{-@ measure isString @-}
isString :: Value -> Bool
isString (S _) = True
isString _     = False
