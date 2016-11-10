{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# LANGUAGE ImplicitParams       #-}
module Test.Target.Targetable
  ( Targetable(..), qquery
  , unfold, apply, unapply
  , oneOf, whichOf
  , constrain, ofReft
  ) where

import           Control.Applicative
import           Control.Arrow                   (second)

import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Char
import qualified Data.HashMap.Strict             as M
import           Data.List
import           Data.Maybe

import           Data.Proxy
import qualified Data.Text                       as T
import           Data.Word                       (Word8)
import           GHC.Generics
import           GHC.Stack

import           Language.Fixpoint.Types         hiding (prop, ofReft, reft)
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types   hiding (var)

import           Test.Target.Expr
import           Test.Target.Eval
import           Test.Target.Monad


import           Test.Target.Util

-- import Debug.Trace

--------------------------------------------------------------------------------
--- Constrainable Data
--------------------------------------------------------------------------------
-- | A class of datatypes for which we can efficiently generate constrained
-- values by querying an SMT solver.
--
-- If possible, instances should not be written by hand, but rather by using the
-- default implementations via "GHC.Generics", e.g.
--
-- > import GHC.Generics
-- > import Test.Target.Targetable
-- >
-- > data Foo = ... deriving Generic
-- > instance Targetable Foo
class Targetable a where
  -- | Construct an SMT query describing all values of the given type up to the
  -- given 'Depth'.
  query   :: (?loc :: CallStack) => Proxy a -> Depth -> Symbol -> SpecType -> Target Symbol

  -- | Reconstruct a Haskell value from the SMT model.
  decode  :: Symbol
             -- ^ the symbolic variable corresponding to the root of the value
          -> SpecType
             -- ^ the type of values we're generating (you can probably ignore this)
          -> Target a

  -- | Check whether a Haskell value inhabits the given type. Also returns a
  -- logical expression corresponding to the Haskell value.
  check   :: a -> SpecType -> Target (Bool, Expr)

  -- | Translate a Haskell value into a logical expression.
  toExpr  :: a -> Expr

  -- | What is the Haskell type? (Mainly used to make the SMT queries more
  -- readable).
  getType :: Proxy a -> Sort

  default getType :: (Generic a, Rep a ~ D1 d f, Datatype d)
                  => Proxy a -> Sort
  getType _ = FObj $ qualifiedDatatypeName (undefined :: Rep a a)

  default query :: (?loc :: CallStack) => (Generic a, GQuery (Rep a))
                => Proxy a -> Int -> Symbol -> SpecType -> Target Symbol
  query p d x t = do
    -- traceShowM ("query")
    -- traceShowM ("query", t)
    gquery (reproxyRep p) d x t

  default toExpr :: (Generic a, GToExpr (Rep a))
                 => a -> Expr
  toExpr = gtoExpr . from

  default decode :: (Generic a, GDecode (Rep a))
                 => Symbol -> SpecType -> Target a
  decode v _ = do
    x <- whichOf v
    (c, fs) <- unapply x
    to <$> gdecode c fs

  default check :: (Generic a, GCheck (Rep a))
                => a -> SpecType -> Target (Bool, Expr)
  check v t = gcheck (from v) t

qquery :: Targetable a => Proxy a -> Int -> SpecType -> Target Symbol
qquery p d t = fresh (getType p) >>= \x -> query p d x t

reproxy :: proxy a -> Proxy b
reproxy _ = Proxy
{-# INLINE reproxy #-}

-- | Given a data constuctor @d@ and a refined type for @d@s output,
-- return a list of types representing suitable arguments for @d@.
unfold :: Symbol -> SpecType -> Target [(Symbol, SpecType)]
unfold cn t = do
  -- traceShowM ("unfold.cn", cn)
  dcp <- lookupCtor cn t
  -- traceShowM ("unfold.dcp")
  -- traceShowM ("unfold.t.r", reft t)
  tyi <- gets tyconInfo
  emb <- gets embEnv
  let ts = applyPreds (addTyConInfo emb tyi t) dcp
  -- traceM "unfold.ts.rs"
  -- mapM_ (traceShowM . rt_reft . snd) ts
  return ts

-- | Given a data constructor @d@ and a list of expressions @xs@, construct a
-- new expression corresponding to @d xs@.
apply :: Symbol -> SpecType -> [Expr] -> Target Expr
apply c t vs = do
  -- traceShowM ("apply")
  -- traceShowM ("apply", c, vs)
  mc <- gets chosen
  case mc of
    Just ch -> mapM_ (addDep ch) vs
    Nothing -> return ()
  let x = app c vs
  t <- lookupCtor c t
  -- traceShowM ("apply.ctor", c, t)
  let (xs, _, _, rt) = bkArrowDeep t
      su             = mkSubst $ zip (map symbol xs) vs
  addConstructor (c, rTypeSort mempty t)
  constrain $ ofReft (subst su $ reft rt) x
  return x


-- | Split a symbolic variable representing the application of a data
-- constructor into a pair of the data constructor and the sub-variables.
unapply :: Symbol -> Target (Symbol, [Symbol])
unapply c = do
  let [_,cn,_] = T.splitOn "-" $ symbolText c
  deps <- gets deps
  return (symbol cn, M.lookupDefault [] c deps)

-- | Given a symbolic variable and a list of @(choice, var)@ pairs,
-- @oneOf x choices@ asserts that @x@ must equal one of the @var@s in
-- @choices@.
oneOf :: Symbol -> [(Expr,Expr)] -> Target ()
oneOf x cs
  = do cs <- forM cs $ \(y,c) -> do
               addDep x c
               constrain $ prop c `imp` (var x `eq` y)
               return $ prop c
       constrain $ pOr cs
       constrain $ pAnd [ PNot $ pAnd [x, y]
                        | [x, y] <- filter ((==2) . length) $ subsequences cs ]

-- | Given a symbolic variable @x@, figure out which of @x@s choice varaibles
-- was picked and return it.
whichOf :: Symbol -> Target Symbol
whichOf v = do
  deps <- gets deps
  let Just cs = M.lookup v deps
  -- traceShowM (v, cs)
  -- FIXME: should be a singleton list...
  c:_  <- catMaybes <$> forM cs (\c -> do
    val <- getValue c
    if val == "true"
      then return (Just c)
      else return Nothing)
  return c


-- | Assert a logical predicate, guarded by the current choice variable.
constrain :: (?loc :: CallStack) => Expr -> Target ()
constrain p = do
  -- traceShowM ("constrain")
  -- traceM (showCallStack ?loc)
  -- traceShowM ("constrain", p)
  mc <- gets chosen
  case mc of
    Nothing -> addConstraint p
    Just c  -> let p' = prop (var c) `imp` p
               in addConstraint p'

-- | Given a refinement @{v | p}@ and an expression @e@, construct
-- the predicate @p[e/v]@.
ofReft :: Reft -> Expr -> Expr
ofReft (Reft (v, p)) e
  = let x = mkSubst [(v, e)]
    in subst x p

--------------------------------------------------------------------------------
--- Instances
--------------------------------------------------------------------------------
instance Targetable () where
  getType _ = FObj "GHC.Tuple.()"
  query _ _ x _ = return x -- fresh (FObj "GHC.Tuple.()")
  -- this is super fiddly, but seemingly required since GHC.exprType chokes on "GHC.Tuple.()"
  toExpr _   = app ("()" :: Symbol) []

  decode _ _ = return ()
  check _ t = do
    let e = app ("()" :: Symbol) []
    b <- eval (reft t) e
    return (b,e)

instance Targetable Int where
  getType _ = FObj "GHC.Types.Int"
  query _ d x t = -- fresh FInt >>= \x ->
    do -- traceShowM ("query.int", var x)
       -- traceShowM ("queyr.int", reft t)
       constrain $ ofReft (reft t) (var x)
       -- use the unfolding depth to constrain the range of Ints, like QuickCheck
       constrain $ var x `ge` fromIntegral (negate d)
       constrain $ var x `le` fromIntegral d
       return x
  toExpr i = ECon $ I $ fromIntegral i

  decode v _ = read . T.unpack <$> getValue v

  check v t = do
    let e = fromIntegral v
    b <- eval (reft t) e
    return (b, e)

instance Targetable Integer where
  getType _ = FObj "GHC.Integer.Type.Integer"
  query _ d x t = query (Proxy :: Proxy Int) d x t
  toExpr  x = toExpr (fromIntegral x :: Int)

  decode v t = decode v t >>= \(x::Int) -> return . fromIntegral $ x

  check v t = do
    let e = fromIntegral v
    b <- eval (reft t) e
    return (b, e)

instance Targetable Char where
  getType _ = FObj "GHC.Types.Char"
  query _ d x t = -- fresh FInt >>= \x ->
    do constrain $ var x `ge` 0
       constrain $ var x `le` fromIntegral d
       constrain $ ofReft (reft t) (var x)
       return x
  toExpr  c = ESym $ SL $ T.singleton c

  decode v t = decode v t >>= \(x::Int) -> return . chr $ x + ord 'a'

  check v t = do
    let e = ESym $ SL $ T.singleton v
    b <- eval (reft t) e
    return (b, e)

instance Targetable Word8 where
  getType _ = FObj "GHC.Word.Word8"
  query _ d x t = -- fresh FInt >>= \x ->
    do _ <- asks depth
       constrain $ var x `ge` 0
       constrain $ var x `le` fromIntegral d
       constrain $ ofReft (reft t) (var x)
       return x
  toExpr i   = ECon $ I $ fromIntegral i

  decode v t = decode v t >>= \(x::Int) -> return $ fromIntegral x

  check v t = do
    let e = fromIntegral v
    b <- eval (reft t) e
    return (b, e)

instance Targetable Bool
  -- getType _ = FObj "GHC.Types.Bool"
  -- query _ _ x t = -- fresh boolsort >>= \x ->
  --   do constrain $ ofReft (reft t) (var x)
  --      return x

  -- decode v _ = getValue v >>= \case
  --   "true"  -> return True
  --   "false" -> return False
  --   x       -> Ex.throwM (SmtError $ "expected boolean, got: " ++ T.unpack x)


instance Targetable a => Targetable [a]
instance Targetable a => Targetable (Maybe a)
instance (Targetable a, Targetable b) => Targetable (Either a b)
instance (Targetable a, Targetable b) => Targetable (a,b)
instance (Targetable a, Targetable b, Targetable c) => Targetable (a,b,c)
instance (Targetable a, Targetable b, Targetable c, Targetable d) => Targetable (a,b,c,d)


-- instance (Num a, Integral a, Targetable a) => Targetable (Ratio a) where
--   getType _ = FObj "GHC.Real.Ratio"
--   query _ d t = query (Proxy :: Proxy Int) d t
--   decode v t= decode v t >>= \ (x::Int) -> return (fromIntegral x)
--   -- query _ d t = fresh (FObj "GHC.Real.Ratio") >>= \x ->
--   --   do query (Proxy :: Proxy Int) d t
--   --      query (Proxy :: Proxy Int) d t
--   --      return x
--   -- stitch d t = do x :: Int <- stitch d t
--   --                 y' :: Int <- stitch d t
--   --                 -- we should really modify `t' above to have Z3 generate non-zero denoms
--   --                 let y = if y' == 0 then 1 else y'
--   --                 let toA z = fromIntegral z :: a
--   --                 return $ toA x % toA y
--   toExpr x = EApp (dummyLoc "GHC.Real.:%") [toExpr (numerator x), toExpr (denominator x)]
--   check = undefined


reproxyRep :: Proxy a -> Proxy (Rep a a)
reproxyRep = reproxy


--------------------------------------------------------------------------------
--- Sums of Products
--------------------------------------------------------------------------------
class GToExpr f where
  gtoExpr      :: f a -> Expr

class GQuery f where
  gquery       :: (?loc :: CallStack) => Proxy (f a) -> Int -> Symbol -> SpecType -> Target Symbol

class GDecode f where
  gdecode      :: Symbol -> [Symbol] -> Target (f a)

class GCheck f where
  gcheck       :: f a -> SpecType -> Target (Bool, Expr)

reproxyGElem :: Proxy (M1 d c f a) -> Proxy (f a)
reproxyGElem = reproxy

instance (Datatype c, GToExprCtor f) => GToExpr (D1 c f) where
  gtoExpr (M1 x) = app (qualify mod (symbolString d)) xs
    where
      mod  = GHC.Generics.moduleName (undefined :: D1 c f a)
      (EVar d, xs) = splitEApp $ gtoExprCtor x

instance (Datatype c, GQueryCtors f) => GQuery (D1 c f) where
  gquery p d x t = inModule mod . making sort $ do
    --traceShowM ("gquery", sort)
    xs <- gqueryCtors (reproxyGElem p) d t
    -- x  <- fresh sort
    oneOf x xs
    constrain $ ofReft (reft t) (var x)
    return x
   where
     mod  = symbol $ GHC.Generics.moduleName (undefined :: D1 c f a)
     sort = FObj $ qualifiedDatatypeName (undefined :: D1 c f a)

instance (Datatype c, GDecode f) => GDecode (D1 c f) where
  gdecode c vs = M1 <$> making sort (gdecode c vs)
    where
      sort = FObj $ qualifiedDatatypeName (undefined :: D1 c f a)

instance (Datatype c, GCheck f) => GCheck (D1 c f) where
  gcheck (M1 x) t = inModule mod . making sort $ gcheck x t
    where
      mod  = symbol $ GHC.Generics.moduleName (undefined :: D1 c f a)
      sort = FObj $ qualifiedDatatypeName (undefined :: D1 c f a)


instance (Targetable a) => GToExpr (K1 i a) where
  gtoExpr (K1 x) = toExpr x

instance (Targetable a) => GQuery (K1 i a) where
  gquery p d _ t = do
    let p' = reproxy p :: Proxy a
    ty <- gets makingTy
    depth <- asks depth
    sc <- asks scDepth
    let d' = if getType p' == ty || sc
                then d
                else depth

    qquery p' d' t

instance Targetable a => GDecodeFields (K1 i a) where
  gdecodeFields (v:vs) = do
    x <- decode v undefined
    return (vs, K1 x)
  gdecodeFields _ = error "gdecodeFields []"

instance Targetable a => GCheckFields (K1 i a) where
  gcheckFields (K1 x) ((f,t):ts) = do
    (b, v) <- check x t
    return (b, [v], subst (mkSubst [(f, v)]) ts)
  gcheckFields _ _ = error "gcheckFields _ []"

qualify :: String -> String -> String
qualify m x = m ++ ('.':x)
{-# INLINE qualify #-}

qualifiedDatatypeName :: Datatype d => D1 d f a -> Symbol
qualifiedDatatypeName d = symbol $ qualify m (datatypeName d)
  where m = GHC.Generics.moduleName d
{-# INLINE qualifiedDatatypeName #-}

--------------------------------------------------------------------------------
--- Sums
--------------------------------------------------------------------------------
class GToExprCtor f where
  gtoExprCtor   :: f a -> Expr

class GQueryCtors f where
  gqueryCtors :: (?loc :: CallStack) => Proxy (f a) -> Int -> SpecType -> Target [(Expr, Expr)]

reproxyLeft :: Proxy ((c (f :: * -> *) (g :: * -> *)) a) -> Proxy (f a)
reproxyLeft = reproxy

reproxyRight :: Proxy ((c (f :: * -> *) (g :: * -> *)) a) -> Proxy (g a)
reproxyRight = reproxy

instance (GToExprCtor f, GToExprCtor g) => GToExprCtor (f :+: g) where
  gtoExprCtor (L1 x) = gtoExprCtor x
  gtoExprCtor (R1 x) = gtoExprCtor x

instance (GQueryCtors f, GQueryCtors g) => GQueryCtors (f :+: g) where
  gqueryCtors p d t = do
    xs <- gqueryCtors (reproxyLeft p) d t
    ys <- gqueryCtors (reproxyRight p) d t
    return $! xs++ys

instance (GDecode f, GDecode g) => GDecode (f :+: g) where
  gdecode c vs =  L1 <$> gdecode c vs
              <|> R1 <$> gdecode c vs

instance (GCheck f, GCheck g) => GCheck (f :+: g) where
  gcheck (L1 x) t = gcheck x t
  gcheck (R1 x) t = gcheck x t


instance (Constructor c, GToExprFields f) => GToExprCtor (C1 c f) where
  gtoExprCtor c@(M1 x)  = app (symbol $ conName c) (gtoExprFields x)

instance (Constructor c, GRecursive f, GQueryFields f) => GQueryCtors (C1 c f) where
  gqueryCtors p d t | d <= 0
    = do ty <- gets makingTy
         if gisRecursive p ty
           then return []
           else pure <$> gqueryCtor p 0 t
  gqueryCtors p d t = pure <$> gqueryCtor p d t

instance (Constructor c, GDecodeFields f) => GDecode (C1 c f) where
  gdecode c vs
    | c == symbol (conName (undefined :: C1 c f a))
    = M1 . snd <$> gdecodeFields vs
    | otherwise
    = empty

instance (Constructor c, GCheckFields f) => GCheck (C1 c f) where
  gcheck (M1 x) t = do
    mod <- symbolString <$> gets modName
    let cn = symbol $ qualify mod (conName (undefined :: C1 c f a))
    ts <- unfold cn t
    (b, vs, _) <- gcheckFields x ts
    let v = app cn vs
    b'  <- eval (reft t) v
    return (b && b', v)

gisRecursive :: (Constructor c, GRecursive f)
             => Proxy (C1 c f a) -> Sort -> Bool
gisRecursive (p :: Proxy (C1 c f a)) t
  = t `elem` gconArgTys (reproxyGElem p)

gqueryCtor :: (?loc :: CallStack) => (Constructor c, GQueryFields f)
           => Proxy (C1 c f a) -> Int -> SpecType -> Target (Expr, Expr)
gqueryCtor (p :: Proxy (C1 c f a)) d t
  = guarded cn $ do
      -- traceShowM ("gqueryCtor", cn, t)
      mod <- symbolString <$> gets modName
      ts  <- unfold (symbol $ qualify mod cn) t
      xs  <- gqueryFields (reproxyGElem p) d ts
      apply (symbol $ qualify mod cn) t xs
  where
    cn = conName (undefined :: C1 c f a)

--------------------------------------------------------------------------------
--- Products
--------------------------------------------------------------------------------
class GToExprFields f where
  gtoExprFields :: f a -> [Expr]

class GRecursive f where
  gconArgTys  :: Proxy (f a) -> [Sort]

class GQueryFields f where
  gqueryFields  :: (?loc :: CallStack) => Proxy (f a) -> Int -> [(Symbol,SpecType)] -> Target [Expr]

class GDecodeFields f where
  gdecodeFields :: [Symbol] -> Target ([Symbol], f a)

class GCheckFields f where
  gcheckFields :: f a -> [(Symbol, SpecType)]
               -> Target (Bool, [Expr], [(Symbol, SpecType)])


instance (GToExprFields f, GToExprFields g) => GToExprFields (f :*: g) where
  gtoExprFields (f :*: g) = gtoExprFields f ++ gtoExprFields g

instance (GRecursive f, GRecursive g) => GRecursive (f :*: g) where
  gconArgTys p = gconArgTys (reproxyLeft p) ++ gconArgTys (reproxyRight p)

instance (GQueryFields f, GQueryFields g) => GQueryFields (f :*: g) where
  gqueryFields p d ts = do
    xs <- gqueryFields (reproxyLeft p) d ts
    let su = mkSubst $ zipWith (\x t -> (fst t, x)) xs ts
    let ts' = drop (length xs) ts
    ys <- gqueryFields (reproxyRight p) d (map (second (subst su)) ts')
    return $ xs ++ ys

instance (GDecodeFields f, GDecodeFields g) => GDecodeFields (f :*: g) where
  gdecodeFields vs = do
    (vs', ls)  <- gdecodeFields vs
    (vs'', rs) <- gdecodeFields vs'
    return (vs'', ls :*: rs)

instance (GCheckFields f, GCheckFields g) => GCheckFields (f :*: g) where
  gcheckFields (f :*: g) ts = do
    (bl,fs,ts')  <- gcheckFields f ts
    (br,gs,ts'') <- gcheckFields g ts'
    return (bl && br, fs ++ gs, ts'')


instance (GToExpr f) => GToExprFields (S1 c f) where
  gtoExprFields (M1 x)     = [gtoExpr x]

instance Targetable a => GRecursive (S1 c (K1 i a)) where
  gconArgTys _ = [getType (Proxy :: Proxy a)]

instance (GQuery f) => GQueryFields (S1 c f) where
  gqueryFields p d (t:_) = sequence [var <$> gquery (reproxyGElem p) (d-1) "" (snd t)]
  gqueryFields _ _ _     = error "gqueryfields _ _ []"

instance GDecodeFields f => GDecodeFields (S1 c f) where
  gdecodeFields vs = do
    (vs', x) <- gdecodeFields vs
    return (vs', M1 x)

instance (GCheckFields f) => GCheckFields (S1 c f) where
  gcheckFields (M1 x) ts = gcheckFields x ts

instance GToExprFields U1 where
  gtoExprFields _ = []

instance GRecursive U1 where
  gconArgTys _    = []

instance GQueryFields U1 where
  gqueryFields _ _ _ = return []

instance GDecodeFields U1 where
  gdecodeFields vs = return (vs, U1)

instance GCheckFields U1 where
  gcheckFields _ ts = return (True, [], ts)
