import Distribution.Simple



main = defaultMain

-- 
-- --- main = defaultMainWithHooks fixpointHooks 
--  
-- fixpointHooks   = defaultUserHooks { postInst = cpFix }
--    where 
--      cpFix _ _ _ lbi = putStrLn $ "CPFIXSAYS: " ++ show lbi  
