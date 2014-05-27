module Class2 where

{-@ LIQUID "--idirs=tests/neg" @-}
{-@ LIQUID "--idirs=../neg" @-}
import Class5

instance Foo ()
