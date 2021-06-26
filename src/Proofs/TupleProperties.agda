module Proofs.TupleProperties where

open import Haskell.Prim
open import Haskell.Prelude
open import Haskell.Data.Bifunctor
open import Proofs.Proof

open Bifunctor ⦃ ... ⦄

propConstructorWrapSecond : (f : b -> c) -> (t : a × b) -> snd (second f t) ≡ f (snd t)
propConstructorWrapSecond f (x , y) = refl