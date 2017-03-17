{-# LANGUAGE Rank2Types, ExistentialQuantification #-}


module Variance where


import Control.Monad.Trans.Except



p1 :: Parser a 
p1 = undefined 

p2 :: Parser a -> ()
p2 _ = () 

p = p2 p1 


-- The following structure is a simplification of 
--  Options.Applicative.Parser 

data Parser a
  = OptP (Option a)

data Option a = Option
  { optMain :: OptReader a }



data OptReader a
 =  CmdReader (String -> Maybe (ParserInfo a)) -- ^ command reader


data ParserInfo a = ParserInfo
  { infoParser :: Parser a    -- ^ the option parser for the program                              -- after arguments (default: True)
  }