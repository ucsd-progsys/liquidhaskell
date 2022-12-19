{- HLINT ignore "Use camelCase" -}
{-@ relMapMap_rtu :: f1:(x1:GHC.Types.Int -> GHC.Types.Int) -> f2:(x2:GHC.Types.Int -> GHC.Types.Int) -> xs1:[GHC.Types.Int] -> xs2:{VV : [GHC.Types.Int] | len xs1 <= len xs2} -> {VV : () | len (UMap.map f1 xs1) <= len (UMap.map f2 xs2)} @-}
relMapMap_rtu :: (GHC.Types.Int -> GHC.Types.Int)
-- -> (GHC.Types.Int -> GHC.Types.Int)
-- -> [GHC.Types.Int]
-- -> [GHC.Types.Int]
-- -> ()
relMapMap_rtu dsl_dCo dsr_dCo dsl_dCp dsr_dCp =
    case dsl_dCp of
        [] ->
            case dsr_dCp of
                [] -> ()
                (:) xr_atz xsr_atA -> ()

        (:) xl_atz xsl_atA ->
            case dsr_dCp of
                [] -> ()
                (:) xr_atz xsr_atA -> (\ (_ :: ()) (_ :: ()) (_ :: ()) (_ :: ()) -> ()) ((\ (_ :: ()) (_ :: ()) -> ()) xl_atz xr_atz) ((\ (_ :: ()) (_ :: ()) -> ()) xl_atz xr_atz) (relMapMap_rtu dsl_dCo dsr_dCo xsl_atA xsr_atA) (relMapMap_rtu dsl_dCo dsr_dCo xsl_atA xsr_atA)


