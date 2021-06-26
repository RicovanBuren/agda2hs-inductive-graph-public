module Proofs.MaybeProperties where

open import Haskell.Data.Maybe
open import Haskell.Prim
open import Haskell.Prelude
open import Proofs.Proof

propIsJustIfThenElse : (bo : Bool) -> (itsJust : a) -> (maybe : Maybe a) -> isJust (if bo then Just itsJust else maybe) ≡ (bo || isJust maybe)
propIsJustIfThenElse true itsJust maybe = refl
propIsJustIfThenElse false itsJust maybe = refl

propIsJustNothing : {a : Set} -> isJust {a} Nothing ≡ false
propIsJustNothing = refl