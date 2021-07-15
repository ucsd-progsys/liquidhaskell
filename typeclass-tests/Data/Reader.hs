module Data.Reader where

data Reader r a = Reader {runReader :: r -> a}

