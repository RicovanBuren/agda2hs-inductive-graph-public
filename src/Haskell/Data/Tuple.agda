module Haskell.Data.Tuple where

open import Haskell.Prim
open import Haskell.Prim.Tuple

-- | Swap the components of a pair.
swap                    : (a × b) -> (b × a)
swap (a , b)              = (b , a)
