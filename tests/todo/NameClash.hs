{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--no-termination" @-}

module LinSpace () where


data PVector = PVector [Integer] [Integer] (Space PVector) -- { 

-- | Orthogonalized vector bn* and squared lattice determinant 
data Space a = Null | Real a Integer

{-@ data PVector = PVector { 
      pec_  :: [Integer]   
    , mu_   :: [Integer] 
    , orth_ :: {v: (Space (PVectorN (len pec_))) | (dim v) = (len mu_)}
    } 
  @-}

{-@ data Space [dim] @-}

{-@ measure dim     :: (Space PVector) -> Int 
    dim (Null)      = 0
    dim (Real pv n) = 1 + (dim (orthSpace pv))
  @-}

{-@ measure spaceVec     :: (Space PVector) -> PVector
    spaceVec (Real pv n) = pv
  @-}

{-@ measure vec :: PVector -> [Integer]
    vec (PVector p m o) = p
  @-}
{-@ measure orthSpace :: PVector -> (Space PVector)
    orthSpace (PVector v m o) = o
  @-}

{-@ measure muCoeff :: PVector -> [Integer]
    muCoeff (PVector p m o) = m 
  @-}


{-@ invariant {v: PVector | (Inv v) }    @-}
{-@ invariant {v: Space | (dim v) >= 0 } @-}

-- RJ: Helpers for defining properties

{-@ predicate Inv V        = (dim (orthSpace V)) = (len (muCoeff V)) @-}
{-@ predicate SameLen  X Y = ((len (vec X))  = (len (vec Y)))  @-}
{-@ predicate SameOrth X Y = ((orthSpace X) = (orthSpace Y)) @-}

-- RJ: Useful type aliases for specs

{-@ type SameSpace X       = {v:PVector | ((Inv v) && (SameLen X v) && (SameOrth X v))} @-}
{-@ type PVectorN N        = {v: PVector | (len (vec v)) = N}   @-} 
{-@ type PVectorP P        = {v: PVector | (SameLen v P)}       @-} 

--------------------


{-@ orthSpace_ :: p:PVector -> (Space (PVectorP p))  @-} 
orthSpace_ (PVector v m o) = o


