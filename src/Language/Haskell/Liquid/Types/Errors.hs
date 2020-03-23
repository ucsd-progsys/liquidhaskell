{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE DerivingVia         #-}

-- | This module contains the *types* related creating Errors.
--   It depends only on Fixpoint and basic haskell libraries,
--   and hence, should be importable everywhere.

module Language.Haskell.Liquid.Types.Errors (
  -- * Generic Error Type
    TError (..)

  -- * Error with Source Context
  , CtxError (..)
  , errorsWithContext

  -- * Subtyping Obligation Type
  , Oblig (..)

  -- * Adding a Model of the context
  , WithModel (..), dropModel

  -- * Panic (unexpected failures)
  , UserError
  , panic
  , panicDoc
  , todo
  , impossible
  , uError
  , sourceErrors
  , errDupSpecs

  -- * Printing Errors
  , ppError
  , ppError'
  , ppTicks
  
  -- * SrcSpan Helpers
  , realSrcSpan
  , unpackRealSrcSpan
  , srcSpanFileMb
  ) where

import           Prelude                      hiding (error)
import           SrcLoc                      
import           FastString
import           HscTypes (srcErrorMessages, SourceError)
import           ErrUtils
import           Bag

import           GHC.Generics
import           Control.DeepSeq
import qualified Control.Exception            as Ex
import           Data.Typeable                (Typeable)
import           Data.Generics                (Data)
import qualified Data.Binary                  as B
import qualified Data.Maybe                   as Mb
import           Data.Aeson                   hiding (Result)
import           Data.Hashable
import qualified Data.HashMap.Strict          as M
import qualified Data.List                    as L 
import           System.Directory
import           System.FilePath
import           Text.PrettyPrint.HughesPJ 
import           Text.Parsec.Error            (ParseError)
import           Text.Parsec.Error            (errorMessages, showErrorMessages)

import           Language.Fixpoint.Types      (pprint, showpp, Tidy (..), PPrint (..), Symbol, Expr)
import qualified Language.Fixpoint.Misc       as Misc
import qualified Language.Haskell.Liquid.Misc     as Misc 
import           Language.Haskell.Liquid.Misc ((<->))
import           Language.Haskell.Liquid.Types.Generics

instance PPrint ParseError where
  pprintTidy _ e = vcat $ tail $ text <$> ls
    where
      ls         = lines $ showErrorMessages "or" "unknown parse error"
                               "expecting" "unexpected" "end of input"
                               (errorMessages e)

--------------------------------------------------------------------------------
-- | Context information for Error Messages ------------------------------------
--------------------------------------------------------------------------------
data CtxError t = CtxError
  { ctErr :: TError t
  , ctCtx :: Doc
  } deriving (Functor)

instance Eq (CtxError t) where
  e1 == e2 = ctErr e1 == ctErr e2

instance Ord (CtxError t) where
  e1 <= e2 = ctErr e1 <= ctErr e2

--------------------------------------------------------------------------------
errorsWithContext :: [TError Doc] -> IO [CtxError Doc]
--------------------------------------------------------------------------------
errorsWithContext es 
  = Misc.concatMapM fileErrors 
  $ Misc.groupList [ (srcSpanFileMb (pos e), e) | e <- es ]

fileErrors :: (Maybe FilePath, [TError Doc]) -> IO [CtxError Doc]
fileErrors (fp, errs) = do 
  fb  <- getFileBody fp 
  return (errorWithContext fb <$> errs) 

errorWithContext :: FileBody -> TError Doc -> CtxError Doc
errorWithContext fb e = CtxError e (srcSpanContext fb (pos e))

srcSpanContext :: FileBody -> SrcSpan -> Doc
srcSpanContext fb sp
  | Just (l, c, l', c') <- srcSpanInfo sp
  = makeContext l c c' (getFileLines fb l l')
  | otherwise
  = empty

srcSpanInfo :: SrcSpan -> Maybe (Int, Int, Int, Int)
srcSpanInfo (RealSrcSpan s) 
              = Just (l, c, l', c')
  where
     l        = srcSpanStartLine s
     c        = srcSpanStartCol  s
     l'       = srcSpanEndLine   s
     c'       = srcSpanEndCol    s
srcSpanInfo _ = Nothing

getFileLines :: FileBody -> Int -> Int -> [String]
getFileLines fb i j = slice (i - 1) (j - 1) fb 

getFileBody :: Maybe FilePath -> IO FileBody
getFileBody Nothing  = 
  return []
getFileBody (Just f) = do 
  b <- doesFileExist f 
  if b then lines <$> Misc.sayReadFile f 
       else return []

type FileBody = [String]

slice :: Int -> Int -> [a] -> [a]
slice i j xs = take (j - i + 1) (drop i xs)

makeContext :: Int -> Int -> Int -> [String] -> Doc
makeContext _ _ _  []  = empty
makeContext l c c' [s] = makeContext1 l c c' s
makeContext l _ _  ss  = vcat $ text " "
                              : (zipWith makeContextLine [l..] ss)
                              ++ [ text " "
                                 , text " " ]

makeContextLine :: Int -> String -> Doc
makeContextLine l s = lnum l <+> text s
  where
    lnum n          = text (show n) <+> text "|"

makeContext1 :: Int -> Int -> Int -> String -> Doc
makeContext1 l c c' s = vcat [ text " "
                             , lnum l <+> (text s $+$ cursor)
                             , text " "
                             , text " "
                             ]
  where
    lnum n            = text (show n) <+> text "|"
    cursor            = blanks (c - 1) <-> pointer (max 1 (c' - c))
    blanks n          = text $ replicate n ' '
    pointer n         = text $ replicate n '^'

--------------------------------------------------------------------------------
-- | Different kinds of Check "Obligations" ------------------------------------
--------------------------------------------------------------------------------

data Oblig
  = OTerm -- ^ Obligation that proves termination
  | OInv  -- ^ Obligation that proves invariants
  | OCons -- ^ Obligation that proves subtyping constraints
  deriving (Eq, Generic, Data, Typeable)
  deriving Hashable via Generically Oblig

instance B.Binary Oblig
instance Show Oblig where
  show OTerm = "termination-condition"
  show OInv  = "invariant-obligation"
  show OCons = "constraint-obligation"

instance NFData Oblig

instance PPrint Oblig where
  pprintTidy _ = ppOblig

ppOblig :: Oblig -> Doc
ppOblig OCons = text "Constraint Check"
ppOblig OTerm = text "Termination Check"
ppOblig OInv  = text "Invariant Check"

--------------------------------------------------------------------------------
-- | Generic Type for Error Messages -------------------------------------------
--------------------------------------------------------------------------------

-- | INVARIANT : all Error constructors should have a pos field

data TError t =
    ErrSubType { pos  :: !SrcSpan
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , tact :: !t
               , texp :: !t
               } -- ^ liquid type error

  | ErrSubTypeModel
               { pos  :: !SrcSpan
               , msg  :: !Doc
               , ctxM  :: !(M.HashMap Symbol (WithModel t))
               , tactM :: !(WithModel t)
               , texp :: !t
               } -- ^ liquid type error with a counter-example

  | ErrFCrash  { pos  :: !SrcSpan
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , tact :: !t
               , texp :: !t
               } -- ^ liquid type error

  | ErrHole    { pos :: !SrcSpan
               , msg :: !Doc
               , ctx :: !(M.HashMap Symbol t)
               , var :: !Doc 
               , thl :: !t 
               } -- ^ hole type 

  | ErrAssType { pos  :: !SrcSpan
               , obl  :: !Oblig
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , cond :: t
               } -- ^ condition failure error

  | ErrParse    { pos  :: !SrcSpan
                , msg  :: !Doc
                , pErr :: !ParseError
                } -- ^ specification parse error

  | ErrTySpec   { pos :: !SrcSpan
                , knd :: !(Maybe Doc)
                , var :: !Doc
                , typ :: !t
                , msg :: !Doc
                } -- ^ sort error in specification

  | ErrTermSpec { pos  :: !SrcSpan
                , var  :: !Doc
                , msg  :: !Doc
                , exp  :: !Expr
                , typ  :: !t
                , msg' :: !Doc
                } -- ^ sort error in specification

  | ErrDupAlias { pos  :: !SrcSpan
                , var  :: !Doc
                , kind :: !Doc
                , locs :: ![SrcSpan]
                } -- ^ multiple alias with same name error

  | ErrDupSpecs { pos :: !SrcSpan
                , var :: !Doc
                , locs:: ![SrcSpan]
                } -- ^ multiple specs for same binder error

  | ErrDupIMeas { pos   :: !SrcSpan
                , var   :: !Doc
                , tycon :: !Doc
                , locs  :: ![SrcSpan]
                } -- ^ multiple definitions of the same instance measure

  | ErrDupMeas  { pos   :: !SrcSpan
                , var   :: !Doc
                , locs  :: ![SrcSpan]
                } -- ^ multiple definitions of the same measure

  | ErrDupField { pos   :: !SrcSpan
                , dcon  :: !Doc
                , field :: !Doc
                } -- ^ duplicate fields in same datacon

  | ErrDupNames { pos   :: !SrcSpan
                , var   :: !Doc
                , names :: ![Doc]
                } -- ^ name resolves to multiple possible GHC vars

  | ErrBadData  { pos :: !SrcSpan
                , var :: !Doc
                , msg :: !Doc
                } -- ^ bad data type specification (?)

  | ErrBadGADT  { pos :: !SrcSpan
                , var :: !Doc
                , msg :: !Doc
                } -- ^ bad data type specification (?)

  | ErrDataCon  { pos :: !SrcSpan
                , var :: !Doc
                , msg :: !Doc
                } -- ^ refined datacon mismatches haskell datacon

  | ErrInvt     { pos :: !SrcSpan
                , inv :: !t
                , msg :: !Doc
                } -- ^ Invariant sort error

  | ErrIAl      { pos :: !SrcSpan
                , inv :: !t
                , msg :: !Doc
                } -- ^ Using  sort error

  | ErrIAlMis   { pos :: !SrcSpan
                , tAs :: !t
                , tUs :: !t
                , msg :: !Doc
                } -- ^ Incompatible using error

  | ErrMeas     { pos :: !SrcSpan
                , ms  :: !Doc
                , msg :: !Doc
                } -- ^ Measure sort error

  | ErrHMeas    { pos :: !SrcSpan
                , ms  :: !Doc
                , msg :: !Doc
                } -- ^ Haskell bad Measure error

  | ErrUnbound  { pos :: !SrcSpan
                , var :: !Doc
                } -- ^ Unbound symbol in specification

  | ErrUnbPred  { pos :: !SrcSpan
                , var :: !Doc
                } -- ^ Unbound predicate being applied

  | ErrGhc      { pos :: !SrcSpan
                , msg :: !Doc
                } -- ^ GHC error: parsing or type checking

  | ErrResolve  { pos  :: !SrcSpan
                , kind :: !Doc
                , var  :: !Doc
                , msg  :: !Doc
                } -- ^ Name resolution error 

  | ErrMismatch { pos   :: !SrcSpan -- ^ haskell type location
                , var   :: !Doc
                , msg   :: !Doc
                , hs    :: !Doc
                , lqTy  :: !Doc
                , diff  :: !(Maybe (Doc, Doc))  -- ^ specific pair of things that mismatch
                , lqPos :: !SrcSpan -- ^ lq type location
                } -- ^ Mismatch between Liquid and Haskell types

  | ErrPartPred { pos  :: !SrcSpan
                , ectr :: !Doc
                , var  :: !Doc
                , argN :: !Int
                , expN :: !Int
                , actN :: !Int
                } -- ^ Mismatch in expected/actual args of abstract refinement

  | ErrAliasCycle { pos    :: !SrcSpan
                  , acycle :: ![(SrcSpan, Doc)]
                  } -- ^ Cyclic Refined Type Alias Definitions

  | ErrIllegalAliasApp { pos   :: !SrcSpan
                       , dname :: !Doc
                       , dpos  :: !SrcSpan
                       } -- ^ Illegal RTAlias application (from BSort, eg. in PVar)

  | ErrAliasApp { pos   :: !SrcSpan
                , dname :: !Doc
                , dpos  :: !SrcSpan
                , msg   :: !Doc
                }

  | ErrTermin   { pos  :: !SrcSpan
                , bind :: ![Doc]
                , msg  :: !Doc
                } -- ^ Termination Error

  | ErrStTerm   { pos  :: !SrcSpan
                , dname :: !Doc
                , msg  :: !Doc
                } -- ^ Termination Error

  | ErrILaw     { pos   :: !SrcSpan
                , cname :: !Doc
                , iname :: !Doc
                , msg   :: !Doc
                } -- ^ Instance Law Error

  | ErrRClass   { pos   :: !SrcSpan
                , cls   :: !Doc
                , insts :: ![(SrcSpan, Doc)]
                } -- ^ Refined Class/Interfaces Conflict

  | ErrMClass   { pos   :: !SrcSpan
                , var   :: !Doc
                } -- ^ Standalone class method refinements

  | ErrBadQual  { pos   :: !SrcSpan
                , qname :: !Doc
                , msg   :: !Doc
                } -- ^ Non well sorted Qualifier

  | ErrSaved    { pos :: !SrcSpan
                , nam :: !Doc
                , msg :: !Doc
                } -- ^ Previously saved error, that carries over after DiffCheck

  | ErrFilePragma { pos :: !SrcSpan
                  }

  | ErrTyCon    { pos    :: !SrcSpan
                , msg    :: !Doc
                , tcname :: !Doc
                }

  | ErrLiftExp  { pos    :: !SrcSpan
                , msg    :: !Doc
                }

  | ErrParseAnn { pos :: !SrcSpan
                , msg :: !Doc
                }

  | ErrNoSpec   { pos  :: !SrcSpan 
                , srcF :: !Doc 
                , bspF :: !Doc
                }

  | ErrOther    { pos   :: SrcSpan
                , msg   :: !Doc
                } -- ^ Sigh. Other.
  
  deriving (Typeable, Generic , Functor )

errDupSpecs :: Doc -> Misc.ListNE SrcSpan -> TError t
errDupSpecs d spans@(sp:_) = ErrDupSpecs sp d spans
errDupSpecs _ _            = impossible Nothing "errDupSpecs with empty spans!"

instance NFData ParseError where
  rnf t = seq t ()

-- FIXME ES: this is very suspicious, why can't we have multiple errors
-- arising from the same span?

instance Eq (TError a) where
  e1 == e2 = errSpan e1 == errSpan e2

instance Ord (TError a) where
  e1 <= e2 = errSpan e1 <= errSpan e2


errSpan :: TError a -> SrcSpan
errSpan =  pos

--------------------------------------------------------------------------------
-- | Simple unstructured type for panic ----------------------------------------
--------------------------------------------------------------------------------
type UserError  = TError Doc

instance PPrint UserError where
  pprintTidy k = ppError k empty . fmap (pprintTidy Lossy)

data WithModel t
  = NoModel t
  | WithModel !Doc t
  deriving (Functor, Show, Eq, Generic)

instance NFData t => NFData (WithModel t)

dropModel :: WithModel t -> t
dropModel m = case m of
  NoModel t     -> t
  WithModel _ t -> t

instance PPrint SrcSpan where
  pprintTidy _ = pprSrcSpan

pprSrcSpan :: SrcSpan -> Doc
pprSrcSpan (UnhelpfulSpan s) = text $ unpackFS s
pprSrcSpan (RealSrcSpan s)   = pprRealSrcSpan s

pprRealSrcSpan :: RealSrcSpan -> Doc
pprRealSrcSpan span
  | sline == eline && scol == ecol =
    hcat [ pathDoc <-> colon
         , int sline <-> colon
         , int scol
         ]
  | sline == eline =
    hcat $ [ pathDoc <-> colon
           , int sline <-> colon
           , int scol
           ] ++ if ecol - scol <= 1 then [] else [char '-' <-> int (ecol - 1)]
  | otherwise =
    hcat [ pathDoc <-> colon
         , parens (int sline <-> comma <-> int scol)
         , char '-'
         , parens (int eline <-> comma <-> int ecol')
         ]
 where
   path  = srcSpanFile      span
   sline = srcSpanStartLine span
   eline = srcSpanEndLine   span
   scol  = srcSpanStartCol  span
   ecol  = srcSpanEndCol    span

   pathDoc = text $ normalise $ unpackFS path
   ecol'   = if ecol == 0 then ecol else ecol - 1

instance Show UserError where
  show = showpp

instance Ex.Exception UserError

-- | Construct and show an Error, then crash
uError :: UserError -> a
uError = Ex.throw

-- | Construct and show an Error, then crash
panicDoc :: {- (?callStack :: CallStack) => -} SrcSpan -> Doc -> a
panicDoc sp d = Ex.throw (ErrOther sp d :: UserError)

-- | Construct and show an Error, then crash
panic :: {- (?callStack :: CallStack) => -} Maybe SrcSpan -> String -> a
panic sp d = panicDoc (sspan sp) (text d)
  where
    sspan  = Mb.fromMaybe noSrcSpan

-- | Construct and show an Error with an optional SrcSpan, then crash
--   This function should be used to mark unimplemented functionality
todo :: {- (?callStack :: CallStack) => -} Maybe SrcSpan -> String -> a
todo s m  = panic s $ unlines
            [ "This functionality is currently unimplemented. "
            , "If this functionality is critical to you, please contact us at: "
            , "https://github.com/ucsd-progsys/liquidhaskell/issues"
            , m
            ]

-- | Construct and show an Error with an optional SrcSpan, then crash
--   This function should be used to mark impossible-to-reach codepaths
impossible :: {- (?callStack :: CallStack) => -} Maybe SrcSpan -> String -> a
impossible s m = panic s $ unlines msg ++ m
   where
      msg = [ "This should never happen! If you are seeing this message, "
            , "please submit a bug report at "
            , "https://github.com/ucsd-progsys/liquidhaskell/issues "
            , "with this message and the source file that caused this error."
            , ""
            ]



-- type CtxError = Error
--------------------------------------------------------------------------------
ppError :: (PPrint a, Show a) => Tidy -> Doc -> TError a -> Doc
--------------------------------------------------------------------------------
ppError k dCtx e = ppError' k dSp dCtx e
  where
    dSp          = pprint (pos e) <-> text ": Error:"

nests :: Foldable t => Int -> t Doc -> Doc
nests n      = foldr (\d acc -> nest n (d $+$ acc)) empty

sepVcat :: Doc -> [Doc] -> Doc
sepVcat d ds = vcat $ L.intersperse d ds

blankLine :: Doc
blankLine    = sizedText 5 " "

ppFull :: Tidy -> Doc -> Doc
ppFull Full  d = d
ppFull Lossy _ = empty

ppReqInContext :: PPrint t => Tidy -> t -> t -> M.HashMap Symbol t -> Doc
ppReqInContext td tA tE c
  = sepVcat blankLine
      [ nests 2 [ text "Inferred type"
                , text "VV :" <+> pprintTidy td tA]
      , nests 2 [ text "not a subtype of Required type"
                , text "VV :" <+> pprintTidy td tE]
      , ppContext td c 
      ]

ppContext :: PPrint t => Tidy -> M.HashMap Symbol t -> Doc 
ppContext td c
  | 0 < length xts = nests 2 [ text "In Context"
                             , vsep (map (uncurry (pprintBind td)) xts)
                             ]
  | otherwise      = empty 
  where 
    xts            = M.toList c 

pprintBind :: PPrint t => Tidy -> Symbol -> t -> Doc
pprintBind td v t = pprintTidy td v <+> char ':' <+> pprintTidy td t

ppReqModelInContext
  :: (PPrint t) => Tidy -> WithModel t -> t -> (M.HashMap Symbol (WithModel t)) -> Doc
ppReqModelInContext td tA tE c
  = sepVcat blankLine
      [ nests 2 [ text "Inferred type"
                , pprintModel td "VV" tA]
      , nests 2 [ text "not a subtype of Required type"
                , pprintModel td "VV" (NoModel tE)]
      , nests 2 [ text "In Context"
                , vsep (map (uncurry (pprintModel td)) (M.toList c))
                ]
      ]

vsep :: [Doc] -> Doc
vsep = vcat . L.intersperse (char ' ')

pprintModel :: PPrint t => Tidy -> Symbol -> WithModel t -> Doc
pprintModel td v wm = case wm of
  NoModel t
    -> pprintTidy td v <+> char ':' <+> pprintTidy td t
  WithModel m t
    -> pprintTidy td v <+> char ':' <+> pprintTidy td t $+$
       pprintTidy td v <+> char '=' <+> pprintTidy td m

ppPropInContext :: (PPrint p, PPrint c) => Tidy -> p -> c -> Doc
ppPropInContext td p c
  = sepVcat blankLine
      [ nests 2 [ text "Property"
                , pprintTidy td p]
      , nests 2 [ text "Not provable in context"
                , pprintTidy td c
                ]
      ]

instance ToJSON RealSrcSpan where
  toJSON sp = object [ "filename"  .= f
                     , "startLine" .= l1
                     , "startCol"  .= c1
                     , "endLine"   .= l2
                     , "endCol"    .= c2
                     ]
    where
      (f, l1, c1, l2, c2) = unpackRealSrcSpan sp

unpackRealSrcSpan :: RealSrcSpan -> (String, Int, Int, Int, Int)
unpackRealSrcSpan rsp = (f, l1, c1, l2, c2)
  where
    f                 = unpackFS $ srcSpanFile rsp
    l1                = srcSpanStartLine rsp
    c1                = srcSpanStartCol  rsp
    l2                = srcSpanEndLine   rsp
    c2                = srcSpanEndCol    rsp


instance FromJSON RealSrcSpan where
  parseJSON (Object v) = realSrcSpan <$> v .: "filename"
                                     <*> v .: "startLine"
                                     <*> v .: "startCol"
                                     <*> v .: "endLine"
                                     <*> v .: "endCol"
  parseJSON _          = mempty

realSrcSpan :: FilePath -> Int -> Int -> Int -> Int -> RealSrcSpan
realSrcSpan f l1 c1 l2 c2 = mkRealSrcSpan loc1 loc2
  where
    loc1                  = mkRealSrcLoc (fsLit f) l1 c1
    loc2                  = mkRealSrcLoc (fsLit f) l2 c2

srcSpanFileMb :: SrcSpan -> Maybe FilePath
srcSpanFileMb (RealSrcSpan s) = Just $ unpackFS $ srcSpanFile s
srcSpanFileMb _               = Nothing 


instance ToJSON SrcSpan where
  toJSON (RealSrcSpan rsp) = object [ "realSpan" .= True, "spanInfo" .= rsp ]
  toJSON (UnhelpfulSpan _) = object [ "realSpan" .= False ]

instance FromJSON SrcSpan where
  parseJSON (Object v) = do tag <- v .: "realSpan"
                            case tag of
                              False -> return noSrcSpan
                              True  -> RealSrcSpan <$> v .: "spanInfo"
  parseJSON _          = mempty

-- Default definition use ToJSON and FromJSON
instance ToJSONKey SrcSpan
instance FromJSONKey SrcSpan

instance (PPrint a, Show a) => ToJSON (TError a) where
  toJSON e = object [ "pos" .= (pos e)
                    , "msg" .= (render $ ppError' Full empty empty e)
                    ]

instance FromJSON (TError a) where
  parseJSON (Object v) = errSaved <$> v .: "pos"
                                  <*> v .: "msg"
  parseJSON _          = mempty

errSaved :: SrcSpan -> String -> TError a
errSaved sp body = ErrSaved sp (text n) (text $ unlines m)
  where
    n : m        = lines body


totalityType :: PPrint a =>  Tidy -> a -> Bool 
totalityType td tE = pprintTidy td tE == text "{VV : Addr# | 5 < 4}"

hint :: TError a -> Doc 
hint e = maybe empty (\d -> "" $+$ ("HINT:" <+> d)) (go e) 
  where 
    go (ErrMismatch {}) = Just "Use the hole '_' instead of the mismatched component (in the Liquid specification)"
    go (ErrBadGADT {})  = Just "Use the hole '_' to specify the type of the constructor" 
    go (ErrSubType {})  = Just "Use \"--no-totality\" to deactivate totality checking."
    go (ErrNoSpec {})   = Just "Run 'liquid' on the source file first."
    go _                = Nothing 

--------------------------------------------------------------------------------
ppError' :: (PPrint a, Show a) => Tidy -> Doc -> Doc -> TError a -> Doc
--------------------------------------------------------------------------------
ppError' td dSp dCtx (ErrAssType _ o _ c p)
  = dSp <+> pprintTidy td o
        $+$ dCtx
        $+$ (ppFull td $ ppPropInContext td p c)

ppError' td dSp dCtx err@(ErrSubType _ _ _ _ tE)
  | totalityType td tE
  = dSp <+> text "Totality Error"
        $+$ dCtx
        $+$ text "Your function is not total: not all patterns are defined." 
        $+$ hint err -- "Hint: Use \"--no-totality\" to deactivate totality checking."

ppError' _td dSp _dCtx (ErrHole _ _ _ x t)
  = dSp <+> "Hole Found"
        $+$ pprint x <+> "::" <+> pprint t 

ppError' td dSp dCtx (ErrSubType _ _ c tA tE)
  = dSp <+> text "Liquid Type Mismatch"
        $+$ dCtx
        $+$ (ppFull td $ ppReqInContext td tA tE c)

ppError' td dSp dCtx (ErrSubTypeModel _ _ c tA tE)
  = dSp <+> text "Liquid Type Mismatch"
        $+$ dCtx
        $+$ (ppFull td $ ppReqModelInContext td tA tE c)

ppError' td  dSp dCtx (ErrFCrash _ _ c tA tE)
  = dSp <+> text "Fixpoint Crash on Constraint"
        $+$ dCtx
        $+$ (ppFull td $ ppReqInContext td tA tE c)

ppError' _ dSp dCtx (ErrParse _ _ e)
  = dSp <+> text "Cannot parse specification:"
        $+$ dCtx
        $+$ (nest 4 $ pprint e)

ppError' _ dSp dCtx (ErrTySpec _ _k v t s)
  = dSp <+> ("Illegal type specification for" <+> ppTicks v) --  <-> ppKind k <-> ppTicks v)
  -- = dSp <+> ("Illegal type specification for" <+> _ppKind k <-> ppTicks v)
        $+$ dCtx
        $+$ nest 4 (vcat [ pprint v <+> Misc.dcolon <+> pprint t
                         , pprint s
                         ])
    where 
      _ppKind Nothing  = empty 
      _ppKind (Just d) = d <-> " "

ppError' _ dSp dCtx (ErrLiftExp _ v)
  = dSp <+> text "Cannot lift" <+> ppTicks v <+> "into refinement logic"
        $+$ dCtx
        $+$ (nest 4 $ text "Please export the binder from the module to enable lifting.")

ppError' _ dSp dCtx (ErrBadData _ v s)
  = dSp <+> text "Bad Data Specification"
        $+$ dCtx
        $+$ (pprint s <+> "for" <+> ppTicks v)

ppError' _ dSp dCtx err@(ErrBadGADT _ v s)
  = dSp <+> text "Bad GADT specification for" <+> ppTicks v
        $+$ dCtx
        $+$ pprint s
        $+$ hint err 

ppError' _ dSp dCtx (ErrDataCon _ d s)
  = dSp <+> "Malformed refined data constructor" <+> ppTicks d
        $+$ dCtx
        $+$ s

ppError' _ dSp dCtx (ErrBadQual _ n d)
  = dSp <+> text "Illegal qualifier specification for" <+> ppTicks n
        $+$ dCtx
        $+$ pprint d

ppError' _ dSp dCtx (ErrTermSpec _ v msg e t s)
  = dSp <+> text "Illegal termination specification for" <+> ppTicks v
        $+$ dCtx
        $+$ (nest 4 $ ((text "Termination metric" <+> ppTicks e <+> text "is" <+> msg <+> "in type signature")
                        $+$ nest 4 (pprint t)
                        $+$ pprint s))

ppError' _ dSp _ (ErrInvt _ t s)
  = dSp <+> text "Bad Invariant Specification"
        $+$ (nest 4 $ text "invariant " <+> pprint t $+$ pprint s)

ppError' _ dSp _ (ErrIAl _ t s)
  = dSp <+> text "Bad Using Specification"
        $+$ (nest 4 $ text "as" <+> pprint t $+$ pprint s)

ppError' _ dSp _ (ErrIAlMis _ t1 t2 s)
  = dSp <+> text "Incompatible Using Specification"
        $+$ (nest 4 $ (text "using" <+> pprint t1 <+> text "as" <+> pprint t2) $+$ pprint s)

ppError' _ dSp _ (ErrMeas _ t s)
  = dSp <+> text "Bad Measure Specification"
        $+$ (nest 4 $ text "measure " <+> pprint t $+$ pprint s)

ppError' _ dSp dCtx (ErrHMeas _ t s)
  = dSp <+> text "Cannot lift Haskell function" <+> ppTicks t <+> text "to logic"
        $+$ dCtx
        $+$ (nest 4 $ pprint s)

ppError' _ dSp dCtx (ErrDupSpecs _ v ls)
  = dSp <+> text "Multiple specifications for" <+> ppTicks v <+> colon
        $+$ dCtx
        $+$ ppSrcSpans ls


ppError' _ dSp dCtx (ErrDupIMeas _ v t ls)
  = dSp <+> text "Multiple instance measures" <+> ppTicks v <+> text "for type" <+> ppTicks t
        $+$ dCtx
        $+$ ppSrcSpans ls

ppError' _ dSp dCtx (ErrDupMeas _ v ls)
  = dSp <+> text "Multiple measures named" <+> ppTicks v
        $+$ dCtx
        $+$ ppSrcSpans ls

ppError' _ dSp dCtx (ErrDupField _ dc x)
  = dSp <+> text "Malformed refined data constructor" <+> dc
        $+$ dCtx
        $+$ (nest 4 $ text "Duplicated definitions for field" <+> ppTicks x)

ppError' _ dSp dCtx (ErrDupNames _ x ns)
  = dSp <+> text "Ambiguous specification symbol" <+> ppTicks x
        $+$ dCtx
        $+$ ppNames ns

ppError' _ dSp dCtx (ErrDupAlias _ k v ls)
  = dSp <+> text "Multiple definitions of" <+> pprint k <+> ppTicks v
        $+$ dCtx
        $+$ ppSrcSpans ls

ppError' _ dSp dCtx (ErrUnbound _ x)
  = dSp <+> text "Unbound variable" <+> pprint x
        $+$ dCtx

ppError' _ dSp dCtx (ErrUnbPred _ p)
  = dSp <+> text "Cannot apply unbound abstract refinement" <+> ppTicks p
        $+$ dCtx

ppError' _ dSp dCtx (ErrGhc _ s)
  = dSp <+> text "GHC Error"
        $+$ dCtx
        $+$ (nest 4 $ pprint s)

ppError' _ dSp dCtx (ErrResolve _ kind v msg)
  = dSp <+> (text "Unknown" <+> kind <+> ppTicks v) 
        $+$ dCtx
        $+$ (nest 4 msg)

ppError' _ dSp dCtx (ErrPartPred _ c p i eN aN)
  = dSp <+> text "Malformed predicate application"
        $+$ dCtx
        $+$ (nest 4 $ vcat
                        [ "The" <+> text (Misc.intToString i) <+> "argument of" <+> c <+> "is predicate" <+> ppTicks p
                        , "which expects" <+> pprint eN <+> "arguments" <+> "but is given only" <+> pprint aN
                        , " "
                        , "Abstract predicates cannot be partially applied; for a possible fix see:"
                        , " "
                        , nest 4 "https://github.com/ucsd-progsys/liquidhaskell/issues/594"
                        ])

ppError' _ dSp dCtx e@(ErrMismatch _ x msg τ t cause hsSp)
  = dSp <+> "Specified type does not refine Haskell type for" <+> ppTicks x <+> parens msg
        $+$ dCtx
        $+$ (sepVcat blankLine
              [ "The Liquid type"
              , nest 4 t
              , "is inconsistent with the Haskell type"
              , nest 4 τ
              , "defined at" <+> pprint hsSp
              , maybe empty ppCause cause 
              ])
    where 
      ppCause (hsD, lqD) = sepVcat blankLine 
              [ "Specifically, the Liquid component" 
              , nest 4 lqD 
              , "is inconsistent with the Haskell component" 
              , nest 4 hsD 
              , hint e 
              ] 

ppError' _ dSp dCtx (ErrAliasCycle _ acycle)
  = dSp <+> text "Cyclic type alias definition for" <+> ppTicks n0
        $+$ dCtx
        $+$ (nest 4 $ sepVcat blankLine (hdr : map describe acycle))
  where
    hdr             = text "The following alias definitions form a cycle:"
    describe (p, n) = text "*" <+> ppTicks n <+> parens (text "defined at:" <+> pprint p)
    n0              = snd . head $ acycle

ppError' _ dSp dCtx (ErrIllegalAliasApp _ dn dl)
  = dSp <+> text "Refinement type alias cannot be used in this context"
        $+$ dCtx
        $+$ text "Type alias:" <+> pprint dn
        $+$ text "Defined at:" <+> pprint dl

ppError' _ dSp dCtx (ErrAliasApp _ name dl s)
  = dSp <+> text "Malformed application of type alias" <+> ppTicks name
        $+$ dCtx
        $+$ (nest 4 $ vcat [ text "The alias" <+> ppTicks name <+> "defined at:" <+> pprint dl
                           , s ] )

ppError' _ dSp dCtx (ErrSaved _ name s)
  = dSp <+> name -- <+> "(saved)"
        $+$ dCtx
        $+$ {- nest 4 -} s

ppError' _ dSp dCtx (ErrFilePragma _)
  = dSp <+> text "Illegal pragma"
        $+$ dCtx
        $+$ text "--idirs, --c-files, and --ghc-option cannot be used in file-level pragmas"

ppError' _ _ _ err@(ErrNoSpec _ srcF bspecF)
  =   vcat [ text "Cannot find .bspec file "
           , nest 4 bspecF 
           , text "for the source file "
           , nest 4 srcF 
           , hint err 
           ]

ppError' _ dSp dCtx (ErrOther _ s)
  = dSp <+> text "Uh oh."
        $+$ dCtx
        $+$ nest 4 s

ppError' _ dSp dCtx (ErrTermin _ xs s)
  = dSp <+> text "Termination Error"
        $+$ dCtx
        <+> (hsep $ L.intersperse comma xs) $+$ s

ppError' _ dSp dCtx (ErrStTerm _ x s)
  = dSp <+> text "Structural Termination Error"
        $+$ dCtx
        <+> (text "Cannot prove termination for size" <+> x) $+$ s
ppError' _ dSp dCtx (ErrILaw _ c i s)
  = dSp <+> text "Law Instance Error"
        $+$ dCtx
        <+> (text "The instance" <+> i <+> text "of class" <+> c <+> text "is not valid.") $+$ s

ppError' _ dSp dCtx (ErrMClass _ v)
  = dSp <+> text "Standalone class method refinement"
    $+$ dCtx
    $+$ (text "Invalid type specification for" <+> v) 
    $+$ (text "Use class or instance refinements instead.")
      
ppError' _ dSp _ (ErrRClass p0 c is)
  = dSp <+> text "Refined classes cannot have refined instances"
    $+$ (nest 4 $ sepVcat blankLine $ describeCls : map describeInst is)
  where
    describeCls
      =   text "Refined class definition for:" <+> c
      $+$ text "Defined at:" <+> pprint p0
    describeInst (p, t)
      =   text "Refined instance for:" <+> t
      $+$ text "Defined at:" <+> pprint p

ppError' _ dSp dCtx (ErrTyCon _ msg ty)
  = dSp <+> text "Illegal data refinement for" <+> ppTicks ty
        $+$ dCtx
        $+$ nest 4 msg

ppError' _ dSp dCtx (ErrParseAnn _ msg)
  = dSp <+> text "Malformed annotation"
        $+$ dCtx
        $+$ nest 4 msg

ppTicks :: PPrint a => a -> Doc
ppTicks = ticks . pprint 

ticks :: Doc -> Doc 
ticks d = text "`" <-> d <-> text "`"

ppSrcSpans :: [SrcSpan] -> Doc
ppSrcSpans = ppList (text "Conflicting definitions at")

ppNames :: [Doc] -> Doc
ppNames ds = ppList "Could refer to any of the names" ds -- [text "-" <+> d | d <- ds]

ppList :: (PPrint a) => Doc -> [a] -> Doc
ppList d ls
  = nest 4 (sepVcat blankLine (d : [ text "*" <+> pprint l | l <- ls ]))

-- | Convert a GHC error into a list of our errors.

sourceErrors :: String -> SourceError -> [TError t]
sourceErrors s = concatMap (errMsgErrors s) . bagToList . srcErrorMessages

errMsgErrors :: String -> ErrMsg -> [TError t]
errMsgErrors s e = [ ErrGhc (errMsgSpan e) msg ]
   where
     msg         =  text s
                $+$ nest 4 (text (show e))
