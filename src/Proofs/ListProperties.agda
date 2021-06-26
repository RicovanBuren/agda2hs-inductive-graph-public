{-# OPTIONS --allow-unsolved-metas #-}
module Proofs.ListProperties where

open import Haskell.Data.List
open import Haskell.Prim
open import Haskell.Prelude
open import Proofs.Proof
open import Proofs.GeneralProperties

---------------------------------
-- Helper functions
---------------------------------
equalLists : ⦃ Eq a ⦄ -> List a -> List a -> Bool
equalLists [] [] = true
equalLists [] (y ∷ ys) = false
equalLists (x ∷ xs) ys = if elem x ys then equalLists xs (delete x ys) else false

disjointLists : ⦃ Eq a ⦄ -> List a -> List a -> Bool
disjointLists [] ys = true
disjointLists (x ∷ xs) ys = if elem x ys then false else disjointLists xs ys

postulate
  -- | Should be correct, otherwise the agda2hs implementation is incorrect
  nullImpliesNonEmpty : (as : List a) -> IsFalse (null as) -> NonEmpty as
  
  -- | Should be equal, otherwise the agda2hs implementation is incorrect
  mapGivesSameLength : {f : (a -> b)} -> (as : List a) -> length as ≡ length (map f as)

  -- | Strict version should produce the same result as lazy version
  propFodlEquivFodl' : (f : b -> a -> b) -> (y : b) -> (xs : List a) -> foldl f y xs ≡ Haskell.Data.List.foldl' f y xs


propNullMap : {f : a -> b} -> (as : List a) -> null as ≡ null (map f as)
propNullMap [] = refl
propNullMap (x ∷ xs) = refl

headIsContained : (ls : List (Int × a)) -> ⦃ nonEmptyInstance : NonEmpty ls ⦄ -> 
  elem (fst (head ls ⦃ nonEmptyInstance ⦄)) (map fst ls) ≡ true
headIsContained ((v , x) ∷ xs) =
  begin
    elem (fst (head ((v , x) ∷ xs) ⦃ itsNonEmpty ⦄)) (map fst ((v , x) ∷ xs))
  =⟨⟩
    elem (fst (v , x)) (map fst ((v , x) ∷ xs))
  =⟨⟩
    elem v (map fst ((v , x) ∷ xs))
  =⟨⟩
    elem v (fst (v , x) ∷ (map fst xs))
  =⟨⟩
    elem v (v ∷ (map fst xs))
  =⟨⟩
    foldMap ⦃ iFoldableList ⦄ ⦃ MonoidDisj ⦄ (v ==_) (v ∷ (map fst xs))
  =⟨⟩
    _<>_ ⦃ MonoidDisj .super ⦄ ((v ==_) v) (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidDisj ⦄ (v ==_) (map fst xs))
  =⟨⟩
    _||_ ((v ==_) v) (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidDisj ⦄ (v ==_) (map fst xs))
  =⟨ cong (λ x -> _||_ x (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidDisj ⦄ (v ==_) (map fst xs))) (sameNodeIsEq v) ⟩
    _||_ true (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidDisj ⦄ (v ==_) (map fst xs))
  =⟨⟩
    true
  ∎

propElemHeadEquivTrue : ⦃ _ : Eq a ⦄ -> (xs : List a) -> ⦃ _ : NonEmpty xs ⦄ -> elem (head xs) xs ≡ true
propElemHeadEquivTrue (x ∷ xs) =
  begin
    elem x (x ∷ xs)
  =⟨⟩
    foldMap ⦃ iFoldableList ⦄ ⦃ MonoidDisj ⦄ (x ==_) (x ∷ xs)
  =⟨⟩
    (x == x || foldMap ⦃ iFoldableList ⦄ ⦃ MonoidDisj ⦄ (x ==_) xs)
  =⟨ propTrueOrFalseEquivTrue (x == x) (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidDisj ⦄ (x ==_) xs) ⦃ subst IsTrue (sym (sameElemIsEq x)) itsTrue ⦄ ⟩
    true
  ∎

propDeleteHeadEquivTail : ⦃ _ : Eq a ⦄ -> (xs : List a) -> ⦃ _ : NonEmpty xs ⦄ -> delete (head xs) xs ≡ tail xs
propDeleteHeadEquivTail (x ∷ xs) = 
  begin
    delete x (x ∷ xs)
  =⟨⟩
    deleteBy (_==_) x (x ∷ xs)
  =⟨⟩
    (if x == x then xs else x ∷ (deleteBy (_==_) x xs))
  =⟨ cong (λ p -> if p then xs else x ∷ (deleteBy (_==_) x xs)) (sameElemIsEq x) ⟩
    xs
  ∎

propEqualLists : {a : Set} -> ⦃ _ : Eq a ⦄ -> (xs : List a) -> equalLists xs xs ≡ true
propEqualLists [] = refl
propEqualLists (x ∷ xs) =
  begin
    equalLists (x ∷ xs) (x ∷ xs)
  =⟨⟩
    (if elem x (x ∷ xs) then equalLists xs (delete x (x ∷ xs)) else false)
  =⟨ cong (λ p -> (if p then equalLists xs (delete x (x ∷ xs)) else false)) (propElemHeadEquivTrue (x ∷ xs)) ⟩
    equalLists xs (delete x (x ∷ xs))
  =⟨ cong (λ p -> equalLists xs p) (propDeleteHeadEquivTail (x ∷ xs)) ⟩
    equalLists xs xs
  =⟨ propEqualLists xs ⟩
    true
  ∎

propEqualListsSameHead : ⦃ _ : Eq a ⦄ -> (h : a) -> (xs : List a) -> (ys : List a) -> equalLists (h ∷ xs) (h ∷ ys) ≡ equalLists xs ys
propEqualListsSameHead {a} h xs ys =
  begin
    equalLists (h ∷ xs) (h ∷ ys)
  =⟨⟩
    (if elem ⦃ iFoldableList ⦄ h (h ∷ ys) then equalLists xs (delete h (h ∷ ys)) else false)
  =⟨ cong (λ p -> (if p then equalLists xs (delete h (h ∷ ys)) else false)) (propElemHeadEquivTrue (h ∷ ys)) ⟩
    equalLists xs (delete h (h ∷ ys))
  =⟨ cong (λ p -> equalLists xs p) (propDeleteHeadEquivTail (h ∷ ys)) ⟩
    equalLists {a} xs ys
  ∎

propEqualListsEquivElem : ⦃ _ : Eq a ⦄ -> (xs : List a) -> (ys : List a) -> (zs : List a) -> ⦃ _ : NonEmpty xs ⦄ -> ⦃ _ : NonEmpty zs ⦄ -> ⦃ IsTrue (equalLists xs zs) ⦄ -> elem (head xs) ys ≡ elem (head zs) ys
propEqualListsEquivElem (x ∷ xs) [] (z ∷ zs) ⦃ itsEqual ⦄ = refl
propEqualListsEquivElem (x ∷ xs) (y ∷ ys) (z ∷ zs) ⦃ itsEqual ⦄ =
  begin
    elem x (y ∷ ys)
  =⟨⟩
    (x == y || elem x ys)
  =⟨ {!   !} ⟩
    (z == y || elem z ys)
  =⟨⟩
    elem z (y ∷ ys)
  ∎

propEqualListsDeleteIfEqual : ⦃ _ : Eq a ⦄ -> (xs : List a) -> (zs : List a) -> ⦃ _ : NonEmpty xs ⦄ -> ⦃ _ : NonEmpty zs ⦄ -> ⦃ IsTrue (equalLists xs zs) ⦄ -> equalLists (tail xs) (delete (head xs) zs) ≡ true
propEqualListsDeleteIfEqual (x ∷ xs) (z ∷ zs) ⦃ itsEqual ⦄ = {!   !}

-- propEqualListsPrependDeleteIfEqual : ⦃ _ : Eq a ⦄ -> (xs : List a) -> (zs : List a) -> ⦃ _ : NonEmpty xs ⦄ -> ⦃ _ : NonEmpty zs ⦄ -> ⦃ IsTrue (equalLists xs zs) ⦄ -> equalLists ((head xs) ∷ delete (head xs) zs) zs ≡ true
-- propEqualListsPrependDeleteIfEqual (x ∷ xs) (z ∷ zs) ⦃ itsEqual ⦄ = {!   !}

propEqualListsEquiv₁ : ⦃ _ : Eq a ⦄ -> (xs : List a) -> (ys : List a) -> (zs : List a) -> ⦃ IsTrue (equalLists xs zs) ⦄ -> equalLists xs ys ≡ equalLists zs ys
propEqualListsEquiv₁ [] ys [] ⦃ itsEqual ⦄ = refl
propEqualListsEquiv₁ (x ∷ xs) ys (z ∷ zs) ⦃ itsEqual ⦄ =
  begin
    equalLists (x ∷ xs) ys
  =⟨⟩
    (if elem x ys then equalLists xs (delete x ys) else false)
  =⟨ propIfBoolElseFalseEquivAnd (elem x ys) (equalLists xs (delete x ys)) ⟩
    elem x ys && equalLists xs (delete x ys)
  -- =⟨ {! cong₂ (λ p ih -> p && ih) (propEqualListsEquivElem (x ∷ xs) (y ∷ ys) (z ∷ zs) ⦃ itsEqual ⦄) (propEqualListsEquiv₁ xs ) !} ⟩
  --   elem z ys && equalLists zs (delete z ys)
  -- =⟨ sym (propIfBoolElseFalseEquivAnd (elem z ys) (equalLists zs (delete z ys))) ⟩
  --   (if elem z ys then equalLists zs (delete z ys) else false)
  =⟨ cong (λ p -> elem x ys && p) (propEqualListsEquiv₁ xs (delete x ys) (delete x (z ∷ zs)) ⦃ subst IsTrue (sym (propEqualListsDeleteIfEqual (x ∷ xs) (z ∷ zs) ⦃ itsNonEmpty ⦄ ⦃ itsNonEmpty ⦄ ⦃ itsEqual ⦄)) itsTrue ⦄ ) ⟩
    elem x ys && equalLists (delete x (z ∷ zs)) (delete x ys)
  =⟨ sym ( propIfBoolElseFalseEquivAnd (elem x ys) (equalLists (delete x (z ∷ zs)) (delete x ys))) ⟩
    (if elem x ys then equalLists (delete x (z ∷ zs)) (delete x ys) else false)
  =⟨⟩
    equalLists (x ∷ (delete x (z ∷ zs))) ys
  =⟨⟩
    (if elem x ys then equalLists (delete x (z ∷ zs)) (delete x ys) else false)
  =⟨ {!   !} ⟩
    (if elem z ys then equalLists zs (delete z ys) else false)
  =⟨⟩
    equalLists (z ∷ zs) ys
  ∎
