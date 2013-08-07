-- | This module contains all the code needed to gracefully exit when something
-- goes wrong. Ideally, all forms of errors/exceptions should go through here. 
-- The idea should be to report the error, the source position that causes it,
-- generate a suitable .json file and then exit.

module Language.Haskell.Liquid.Result (
    Error (..)
  , exitWithError
  ) where

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.GhcMisc          (pprDoc)

------------------------------------------------------------------------
-- | Error Data Type ---------------------------------------------------
------------------------------------------------------------------------

data Output = Verified | Err [Error]

data Error  = 
    LiquidType  { pos :: !SrcSpan
                , exp :: !SpecType
                , act :: !SpecType
                , msg :: !String
                } -- ^ liquid type error

  | LiquidParse { pos :: !SrcSpan
                , msg :: !String
                } -- ^ specification parse error

  | LiquidSort  { pos :: !SrcSpan
                , msg :: !String
                } -- ^ sort error in specification

  | Ghc         { pos :: !SrcSpan
                , msg :: !String
                } -- ^ GHC error: parsing or type checking

------------------------------------------------------------------------
-- | Converting Results To Answers -------------------------------------
------------------------------------------------------------------------

class Result a where
  answer :: a -> Answer 



------------------------------------------------------------------------
-- | Rendering Errors---------------------------------------------------
------------------------------------------------------------------------

instance PPrint Error where
  showpp = ppError

ppError :: Error -> Doc
ppError = pprDoc . pos

------------------------------------------------------------------------
-- | Exit Function -----------------------------------------------------
------------------------------------------------------------------------

exitWithAnswer 


