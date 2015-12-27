-- | The below gives a reasonable error message when
--   we REMOVE the liquid signature (with the termination metric)
--   but gives an incomprehensible "termination error" otherwise.
--   # Issue 1. Why?!
--
-- | The above error goes away if you give an explicit HS type
--   signature, which causes a different GHC core term to be analyzed.
--   I suppose this is because the refined-type is for the top-level
--   binder, not the inner-letrec. BUT THEN, we should produce
--   THE SAME ERROR as if there was NO refined-signature AND add to
--   the error message, "Please make sure you add a HS type signature too"

module Blank  where

{-@ spacePrefix :: _ -> s:_ -> _ / [len s] @-}

-- spacePrefix :: String -> String -> Bool
spacePrefix str (c:cs)
  | isSpace c   = spacePrefix str cs
  | otherwise   = take (length str) (c:cs) == str
spacePrefix _ _ = False

isSpace :: Char -> Bool
isSpace = undefined


{- This is GHC core _without_ the signature:
[ Blank.spacePrefix :: [GHC.Types.Char] -> [GHC.Types.Char] -> GHC.Types.Bool
 [LclIdX, Str=DmdType]
 Blank.spacePrefix =
   let {
     $dEq_a16t :: GHC.Classes.Eq [GHC.Types.Char]
     [LclId, Str=DmdType]
     $dEq_a16t =
       GHC.Classes.$fEq[] @ GHC.Types.Char GHC.Classes.$fEqChar } in
   letrec {
     spacePrefix [Occ=LoopBreaker]
       :: [GHC.Types.Char] -> [GHC.Types.Char] -> GHC.Types.Bool
     [LclId, Str=DmdType]
     spacePrefix =
       \ (str :: [GHC.Types.Char]) (ds_d16X :: [GHC.Types.Char]) ->
         case ds_d16X of lq_anf$_d172 {
           [] ->
             (\ _ [Occ=Dead, OS=OneShot] -> GHC.Types.False) GHC.Prim.void#;
           : c cs ->
             let {
               lq_anf$_d173 :: GHC.Types.Bool
               [LclId, Str=DmdType]
               lq_anf$_d173 = Blank.isSpace c } in
             case lq_anf$_d173 of lq_anf$_d174 {
               GHC.Types.False ->
                 (\ _ [Occ=Dead, OS=OneShot] ->
                    let {
                      lq_anf$_d175 :: GHC.Types.Int
                      [LclId, Str=DmdType]
                      lq_anf$_d175 =
                        Data.Foldable.length
                          @ [] Data.Foldable.$fFoldable[] @ GHC.Types.Char str } in
                    let {
                      lq_anf$_d176 :: [GHC.Types.Char]
                      [LclId, Str=DmdType]
                      lq_anf$_d176 = GHC.Types.: @ GHC.Types.Char c cs } in
                    let {
                      lq_anf$_d177 :: [GHC.Types.Char]
                      [LclId, Str=DmdType]
                      lq_anf$_d177 =
                        GHC.List.take @ GHC.Types.Char lq_anf$_d175 lq_anf$_d176 } in
                    GHC.Classes.== @ [GHC.Types.Char] $dEq_a16t lq_anf$_d177 str)
                   GHC.Prim.void#;
               GHC.Types.True -> spacePrefix str cs
             }
         }; } in
   spacePrefix]

 -}

{- This is GHC core _with_ the signature

*************** Transform Rec Expr CoreBinds *****************
[Blank.isSpace :: GHC.Types.Char -> GHC.Types.Bool
 [LclIdX, Str=DmdType]
 Blank.isSpace =
   GHC.Err.undefined @ (GHC.Types.Char -> GHC.Types.Bool),
 $dEq_a16d :: GHC.Classes.Eq [GHC.Types.Char]
 [LclId, Str=DmdType]
 $dEq_a16d =
   GHC.Classes.$fEq[] @ GHC.Types.Char GHC.Classes.$fEqChar,
 Blank.spacePrefix [Occ=LoopBreaker]
   :: GHC.Base.String -> GHC.Base.String -> GHC.Types.Bool
 [LclIdX, Str=DmdType]
 Blank.spacePrefix =
   \ (str :: GHC.Base.String) (ds_d16D :: [GHC.Types.Char]) ->
     case ds_d16D of lq_anf$_d16I {
       [] ->
         (\ _ [Occ=Dead, OS=OneShot] -> GHC.Types.False) GHC.Prim.void#;
       : c cs ->
         let {
           lq_anf$_d16J :: GHC.Types.Bool
           [LclId, Str=DmdType]
           lq_anf$_d16J = Blank.isSpace c } in
         case lq_anf$_d16J of lq_anf$_d16K {
           GHC.Types.False ->
             (\ _ [Occ=Dead, OS=OneShot] ->
                let {
                  lq_anf$_d16L :: GHC.Types.Int
                  [LclId, Str=DmdType]
                  lq_anf$_d16L =
                    Data.Foldable.length
                      @ [] Data.Foldable.$fFoldable[] @ GHC.Types.Char str } in
                let {
                  lq_anf$_d16M :: [GHC.Types.Char]
                  [LclId, Str=DmdType]
                  lq_anf$_d16M = GHC.Types.: @ GHC.Types.Char c cs } in
                let {
                  lq_anf$_d16N :: [GHC.Types.Char]
                  [LclId, Str=DmdType]
                  lq_anf$_d16N =
                    GHC.List.take @ GHC.Types.Char lq_anf$_d16L lq_anf$_d16M } in
                GHC.Classes.== @ [GHC.Types.Char] $dEq_a16d lq_anf$_d16N str)
               GHC.Prim.void#;
           GHC.Types.True -> Blank.spacePrefix str cs
         }
     };]
*************** Slicing Out Unchanged CoreBinds *****************


 -}
