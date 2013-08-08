{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}

-- | This module contains all the code needed to output the result which 
--   is either: `SAFE` or `WARNING` with some reasonable error message when 
--   something goes wrong. All forms of errors/exceptions should go through 
--   here. The idea should be to report the error, the source position that 
--   causes it, generate a suitable .json file and then exit.

module Language.Haskell.Liquid.Result (
  -- * Single Exit Function
   exitWithResult

  -- * Extra Outputs
  , Output (..)
  ) where

import Name
import SrcLoc                                   (SrcSpan)
import Language.Fixpoint.Misc
import Language.Fixpoint.Files
import Language.Fixpoint.Types
import Language.Fixpoint.Names                  (dropModuleNames)
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Annotate
import Language.Haskell.Liquid.GhcMisc          (pprDoc)
import Text.PrettyPrint.HughesPJ    
import Control.DeepSeq
import Control.Monad
import Data.Maybe
import Data.Monoid
import Data.List                                (sortBy)
import Data.Function                            (on)
import qualified Data.HashMap.Strict as M

------------------------------------------------------------------------
-- | Exit Function -----------------------------------------------------
------------------------------------------------------------------------

exitWithResult :: (Result r) => FilePath -> r -> Maybe Output -> IO (FixResult Error)
exitWithResult target r o = writeExit target (result r) $ fromMaybe emptyOutput o

writeExit target r out   = do {-# SCC "annotate" #-} annotate target r (o_soln out) (o_annot out)
                              donePhase Loud "annotate"
                              let rs = showFix r
                              donePhase (colorResult r) rs 
                              writeFile (extFileName Result target) rs 
                              writeWarns     $ o_warns out 
                              writeCheckVars $ o_vars  out 
                              return r

writeWarns []            = return () 
writeWarns ws            = colorPhaseLn Angry "Warnings:" "" >> putStrLn (unlines ws)

writeCheckVars Nothing   = return ()
writeCheckVars (Just ns) = colorPhaseLn Loud "Checked Binders:" "" >> forM_ ns (putStrLn . dropModuleNames . showpp)

------------------------------------------------------------------------
-- | Stuff To Output ---------------------------------------------------
------------------------------------------------------------------------

data Output = O { o_vars   :: Maybe [Name] 
                , o_warns  :: [String]
                , o_soln   :: FixSolution 
                , o_annot  :: !(AnnInfo Annot)
                }

emptyOutput = O Nothing [] M.empty mempty 
------------------------------------------------------------------------
-- | Rendering Errors---------------------------------------------------
------------------------------------------------------------------------

instance Fixpoint (FixResult Error) where
  toFix Safe           = text "Safe"
  toFix UnknownError   = text "Unknown Error!"
  toFix (Crash xs msg) = vcat $ text "Crash!"  : pprErrs "CRASH:   " xs ++ [parens (text msg)] 
  toFix (Unsafe xs)    = vcat $ text "Unsafe:" : pprErrs "WARNING: " xs

pprErrs :: String -> [Error] -> [Doc] 
pprErrs msg = map ((text msg <+>) . pprint) . sortBy (compare `on` pos) 

-- instance PPrint Cinfo where
--   pprint (Ci src e)  = pprDoc src <+> maybe empty pprint e

-- instance F.Fixpoint Cinfo where
--   toFix = pprint

instance PPrint SrcSpan where
  pprint = pprDoc

instance PPrint Error where
  pprint = ppError

------------------------------------------------------------------------
ppError :: Error -> Doc
------------------------------------------------------------------------
ppError (LiquidType l s tA tE) 
  = text "Liquid Type Error:" <+> pprint l 
    $+$ (nest 4 $ text "Required Type:" <+> pprint tE)
    $+$ (nest 4 $ text "Actual   Type:" <+> pprint tA)

ppError (LiquidParse l s)       
  = text "Error Parsing Specification:" <+> pprint l
    $+$ (nest 4 $ text s)

ppError (LiquidSort l s)       
  = text "Sort Error In Specification:" <+> pprint l
    $+$ (nest 4 $ text s)

ppError (Ghc l s)       
  = text "Invalid Source:" <+> pprint l
    $+$ (nest 4 $ text s) 

ppError (Other l s)       
  = text "Unexpected Error: " <+> pprint l
    $+$ (nest 4 $ text s)



