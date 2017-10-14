module spec Data.String where

measure stringlen :: a -> GHC.Types.Int

Data.String.fromString
    ::  forall a. Data.String.IsString a
    =>  i : [GHC.Types.Char]
    ->  { o : a | len i == stringlen o }
