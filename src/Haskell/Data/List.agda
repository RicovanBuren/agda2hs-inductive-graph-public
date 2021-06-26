module Haskell.Data.List where
-- {-# FOREIGN AGDA2HS {-# Language ScopedTypeVariables #-} #-}

open import Agda.Builtin.List public
open import Agda.Builtin.Strict

open import Haskell.Prim
open import Haskell.Prelude hiding (elem)

-- The 'deleteBy' function behaves like 'delete', but
-- takes a user-supplied equality predicate.
deleteBy                : {a : Set} -> (a -> a -> Bool) -> a -> List a -> List a
deleteBy _  _ []        = []
deleteBy eq x (y ∷ ys) = if eq x y then ys else y ∷ (deleteBy eq x ys)

-- It is a special case of 'deleteBy', which allows the programmer to
-- supply their own equality test.
delete : {a : Set} -> ⦃ Eq a ⦄ -> a -> List a -> List a
delete =  deleteBy _==_

-- Ported foldl' using strict
foldl'                  : ∀ {a b} -> (b -> a -> b) -> b -> List a -> b
foldl' {a} {b} f z0 xs  = foldr f' id xs z0
    where
        f'          : a -> (b -> b) -> b -> b
        f' x k z    = k $! f z x

-- | The 'groupBy' function is the non-overloaded version of 'group'.
-- Use terminating to say that this function terminates, because it is a copy of the Data.List.groupBy
{-# TERMINATING #-}
groupBy             : ∀ {a} -> (a -> a -> Bool) -> List a -> List (List a)
groupBy _ []        = []
groupBy f (x ∷ xs)  = (x ∷ ys) ∷ groupBy f zs
                        where
                            tu = span (f x) xs
                            ys = fst tu
                            zs = snd tu

-- The non-overloaded version of 'insert'.
insertBy        : {a : Set} -> (a -> a -> Ordering) -> a -> List a -> List a
insertBy _ x [] = x ∷ []
insertBy cmp x ys@(y ∷ ys')
    = case cmp x y of
        λ   { GT -> y ∷ insertBy cmp x ys'
            ; _  -> x ∷ ys}

sortBy      : {a : Set} -> (a -> a -> Ordering) -> List a -> List a
sortBy cmp  = foldr (insertBy cmp) []

sort : ⦃ Ord a ⦄ -> List a -> List a
sort = sortBy compare

infix 5 _\\_
_\\_ : {a : Set} ⦃ eqa : Eq a ⦄ -> List a -> List a -> List a
_\\_ =  foldl (flip delete)


-- Function for [i..n]
-- Terminates since x gets closer to y
{-# TERMINATING #-}
createList : Int -> Int -> List Int
createList x y with x > y
createList x y | true = []
createList x y | false = x ∷ createList (x + 1) y

-- Support for non unicode list constructor.
_::_ : a -> List a -> List a
_::_ = _∷_