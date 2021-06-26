module GHC.Tuple where

open import Haskell.Prim
open import Haskell.Prelude

_×_×_×_ : (a b c d : Set) → Set
a × b × c × d = Tuple (a ∷ b ∷ c ∷ d ∷ [])

infix 3 _×_×_×_

pattern _,_,_,_   x y z zz   = x Tuple.∷ y Tuple.∷ z Tuple.∷ zz Tuple.∷ []

infix -1 _,_,_,_