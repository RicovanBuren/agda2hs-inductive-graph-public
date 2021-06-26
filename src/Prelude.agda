module Prelude where

open import Haskell.Prim
open import Haskell.Prelude
open import Haskell.Prim.List
open import Haskell.Prim.Foldable
open import Haskell.Prim.Ord
open import Haskell.Prim.Tuple
open import Haskell.Prim.Num

maximum : ⦃ orda : Ord a ⦄ -> (as : List a) -> ⦃ NonEmpty as ⦄ -> a
maximum (x ∷ xs) = foldr max x xs

minimum : ⦃ orda : Ord a ⦄ -> (as : List a) -> ⦃ NonEmpty as ⦄ -> a
minimum (x ∷ xs) = foldr min x xs

foldr1 : (a -> a -> a) -> (as : List a) -> ⦃ NonEmpty as ⦄ -> a
foldr1 f (x ∷ []) = x
foldr1 f (x₁ ∷ x₂ ∷ xs) = f x₁ (foldr1 f (x₂ ∷ xs) ⦃ itsNonEmpty ⦄ )
