{-@ LIQUID "--stringtheory" @-}
module StringOps where

{-@ testStrLen :: { strLen "a" == 1 } @-}
testStrLen :: ()
testStrLen = ()

{-@ testSubString :: { subString "abc" 1 2 == "bc" } @-}
testSubString :: ()
testSubString = ()

{-@ testStrConcat :: { strConcat "a" "b" == "ab" } @-}
testStrConcat :: ()
testStrConcat = ()

{-@ testStrPrefixOf :: { strPrefixOf "a" "abc" && not (strPrefixOf "c" "abc") } @-}
testStrPrefixOf :: ()
testStrPrefixOf = ()

{-@ testStrSuffixOf :: { strSuffixOf "c" "abc" && not (strSuffixOf "a" "abc") } @-}
testStrSuffixOf :: ()
testStrSuffixOf = ()

{-@ testStrContains :: { strContains "abc" "b" && not (strContains "abc" "d") } @-}
testStrContains :: ()
testStrContains = ()
