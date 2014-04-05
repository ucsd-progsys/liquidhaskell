module Fixme where


{-@ LIQUID "--no-termination" @-}
data TokenType
-- k_1873[lq_tmp_x1871:=ds_d1gi]  Char vs [Char] !!!
-- lq_tmp_x1871  goes into g for 901 -- guess from rbsplit
glue ("`":rest1) =				-- `varid` -> varop
  case glue rest1 of
    (qn:"`":rest2) -> ("`"++qn++"`"): glue rest2
    _             -> "`": glue rest1
glue (s:ss)       | all (=='-') s && length s >=2	-- eol comment
                  = (s++concat c): glue rest3
                  where (c,rest3) = break ('\n'`elem`) ss
glue ("(":ss) = case rest5 of
                ")":rest6 {- ds_d1gi : rest6 -} -> ("(" ++ concat tuple ++ ")") : glue rest6
                -- _         -> "(" : glue ss
              where (tuple,rest5) = span (==",") ss
-- glue ("[":"]":ss) = "[]" : glue ss
-- glue ("\n":"#":ss)= "\n" : ('#':concat line) : glue rest
--                   where (line,rest) = break ('\n'`elem`) ss
-- glue (s:ss)       = s: glue ss
-- glue []           = []

-- Deal with comments.
nestcomment :: Int -> String -> (String,String)
nestcomment n ('{':'-':ss) | n>=0 = (("{-"++cs),rm)
                                  where (cs,rm) = nestcomment (n+1) ss
-- nestcomment n ('-':'}':ss) | n>0  = (("-}"++cs),rm)
--                                   where (cs,rm) = nestcomment (n-1) ss
-- nestcomment n ('-':'}':ss) | n==0 = ("-}",ss)
-- nestcomment n (s:ss)       | n>=0 = ((s:cs),rm)
--                                   where (cs,rm) = nestcomment n ss
-- nestcomment n [] = ([],[])


