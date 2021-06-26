module Haskell.Data.Maybe where

open import Haskell.Prim
open import Haskell.Prelude

isJust         : Maybe a -> Bool
isJust Nothing = false
isJust _       = true

fromMaybe     : {a : Set} -> a -> Maybe a -> a
fromMaybe e Nothing = e
fromMaybe e (Just x) = x

fromJust : {a : Set} -> (ma : Maybe a) -> ⦃ IsTrue (isJust ma) ⦄ → a
fromJust (Just x) = x