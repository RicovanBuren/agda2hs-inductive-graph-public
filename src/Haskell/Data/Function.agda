module Haskell.Data.Function where

open import Haskell.Prelude

on : (b -> b -> c) -> (a -> b) -> a -> a -> c
on g f = λ {x y -> g (f x) (f y)}