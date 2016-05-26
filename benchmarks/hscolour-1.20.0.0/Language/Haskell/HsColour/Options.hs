module Language.Haskell.HsColour.Options
  ( Option(..)
  , Output(..)
  , TerminalType(..)
  ) where 

{-@ LIQUID "--totality" @-}

import Language.Haskell.HsColour.Output

-- | Command-line options
data Option =
    Help		-- ^ print usage message
  | Version		-- ^ report version
  | Information		-- ^ report auxiliary information, e.g. CSS defaults
  | Format Output	-- ^ what type of output to produce
  | LHS Bool		-- ^ literate input (i.e. multiple embedded fragments)
  | Anchors Bool	-- ^ whether to add anchors
  | Partial Bool	-- ^ whether to produce a full document or partial
  | Input FilePath	-- ^ input source file
  | Output FilePath	-- ^ output source file
  | Annot FilePath  -- ^ annotations file
  deriving Eq
