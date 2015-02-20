module MovieClient where
import DataBase


import Data.Maybe (catMaybes)

import Prelude hiding (product)

import Control.Applicative ((<$>))

data Tag   = Title | Director | Stars | Year 
            deriving (Show, Eq)

data Value = I Int | S Name  
            deriving (Show, Eq)

data Name = ChickenPlums | TalkToHer | Persepolis | FunnyGames 
          | Paronnaud    | Almadovar | Haneke 
            deriving (Show, Eq)

{-@ type Movies      = [MovieScheme] @-}
{-@ type MovieScheme = Dict Tag Value @-}

type Movies    = Table Tag Value 
type Titles    = Table Tag Value 
type Directors = Table Tag Value

type MovieScheme = Dict Tag Value

movies :: Movies 
movies = fromList [movie1, movie2, movie3, movie4]

movie1, movie2, movie3, movie4 :: MovieScheme
movie1 = mkMovie (S TalkToHer)    (S Almadovar) (I 8) (I 2002) 
movie2 = mkMovie (S ChickenPlums) (S Paronnaud) (I 7) (I 2011)
movie3 = mkMovie (S Persepolis)   (S Paronnaud) (I 8) (I 2007)
movie4 = mkMovie (S FunnyGames)   (S Haneke)    (I 7) (I 2007) 

mkMovie :: Value -> Value -> Value -> Value -> MovieScheme
mkMovie t d s y = (Title := t) += (Stars := s) += (Director := d) += (Year := y) += empty

seen :: Titles
seen = fromList [t1, t2]
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
   isGoodMovie Stars    (I s) = s >= 8
   isGoodMovie Director d     = d `elem` (values Director good_directors)
   isGoodMovie _        _     = True

directors :: Directors
directors = project [Director] movies

good_directors     = directors `diff` not_good_directors
not_good_directors = project [Director, Stars] movies `diff` (directors `product` good_stars)
good_stars         = mk_star_table 8 `union` mk_star_table 9 `union` mk_star_table 10  
mk_star_table s    = singleton ((Stars := I s) += empty)
