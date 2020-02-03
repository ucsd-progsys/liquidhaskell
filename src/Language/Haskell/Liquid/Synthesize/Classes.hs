module Language.Haskell.Liquid.Synthesize.Classes (toMethods) where

import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Types
import           Debug.Trace

import           Language.Haskell.Liquid.GHC.TypeRep

import           TyCon
import           Class
import           Var
import           Name

import           ConLike
import           PatSyn
import           Language.Fixpoint.Types.PrettyPrint

absTySig :: CGInfo -> Type -> Type
absTySig i (ForAllTy v t) = ForAllTy v (absTySig i t)
absTySig _ (TyVarTy v) =
    trace (" Var = " ++ show v ++ " with type " ++ showTy (varType v))
        $ TyVarTy v
absTySig i (AppTy t1 t2) = AppTy (absTySig i t1) (absTySig i t2)
absTySig i (FunTy t1 t2) = FunTy (absTySig i t1) (absTySig i t2)
absTySig info (TyConApp tyCon what) =
    trace
            (  " [ TyConApp ] "
            ++ show (map (isInstanceOf tyCon) (filterTCs info))
            ++ "\n"
            )
        $ TyConApp tyCon (map (absTySig info) what)
absTySig _ _ = error "Entered wildcard"

-- | Entry point.
toMethods :: CGInfo -> [(Var, Type)]
toMethods info = fltMethods
    where   filtered   = filterTCs info 
            methods    = getMethods filtered 
            fltMethods = filterMethods methods 

-- | Get the type signatures of @foldr@, @fmap@, @mappend@, @mempty@
filterMethods :: [(Id, Type)] -> [(Id, Type)]
filterMethods = filter fltMethodsPred

isInstanceOf :: TyCon -> TyCon -> Bool
isInstanceOf tc tyCon = case tyConClass_maybe tyCon of
    Nothing  -> error (" [ isInstanceOf ] tyCon isn't a class " ++ show tyCon)
    Just cls -> tc `notElem` classATs cls

fltMethodsPred :: (Id, Type) -> Bool
fltMethodsPred (i, x) =
       show i
    == "Data.Foldable.foldr"
    || show i
    == "GHC.Base.fmap"
    || show i
    == "GHC.Base.mempty"
    || show i
    == "GHC.Base.mappend"


-- | Get type class methods and the types of the methods
--    @_1@ is the list @TyCon@ that correspond to type class definitions
getMethods :: [TyCon] -> [(Id, Type)]
getMethods []       = []
getMethods (t : ts) = case tyConClass_maybe t of
    Nothing  -> getMethods ts
    Just cls -> map (\x -> (x, varType x)) (classMethods cls) ++ getMethods ts

-- | Filter by name predicate: @Foldable@, @Functor@, @Monoid@,
--   @tyCon@ should be a type class definition. 
filterTCs :: CGInfo -> [TyCon]
filterTCs info = filter filterPred tcTyCons
  where
    tyThings = getTyThings info
    tcTyCons = tyThingsMatch tyThings

filterPred :: TyCon -> Bool
filterPred tyCon =
    let nameOfClass = getOccString $ TyCon.tyConName tyCon
    in     "Foldable"
        == nameOfClass
        || "Functor"
        == nameOfClass
        || "Monoid"
        == nameOfClass

getTyThings :: CGInfo -> [TyThing]
getTyThings info = gsTyThings $ giSrc (ghcI info)

tyThingsMatch :: [TyThing] -> [TyCon]
tyThingsMatch []       = []
tyThingsMatch (t : ts) = case tyThingMatch t of
    Nothing -> tyThingsMatch ts
    Just t0 -> t0 : tyThingsMatch ts
  where
    tyThingMatch (ATyCon tyCon) =
        if isClassTyCon tyCon then Just tyCon else Nothing
    tyThingMatch (AnId id) = -- trace ( " [ TyThing ] " ++ show id ) $
        Nothing
    tyThingMatch (AConLike conLike) = case conLike of
        RealDataCon dtCon -> trace (" [ AConLike ] " ++ show dtCon) Nothing
        PatSynCon pSyn ->
            trace (" [ PSyn ] " ++ show (patSynName pSyn)) Nothing
    tyThingMatch _ = Nothing

getClass :: TyCon -> String
getClass tyCon = case tyConClass_maybe tyCon of
    Nothing -> []
    Just c  -> show (map (\x -> (x, showTy $ varType x)) (classMethods c))

