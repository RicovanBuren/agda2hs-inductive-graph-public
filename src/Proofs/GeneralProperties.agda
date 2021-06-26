module Proofs.GeneralProperties where

open import Proofs.Proof
open import Haskell.Prim
open import Haskell.Prelude

propIsTrueAndTrueFst : (bo₁ : Bool) -> (bo₂ : Bool) -> ⦃ IsTrue (bo₁ && bo₂) ⦄ -> bo₁ ≡ true
propIsTrueAndTrueFst true true = refl

propIsTrueAndTrueSnd : (bo₁ : Bool) -> (bo₂ : Bool) -> ⦃ IsTrue (bo₁ && bo₂) ⦄ -> bo₂ ≡ true
propIsTrueAndTrueSnd true true = refl

propIsTrueIsJustTrue : (bo : Bool) -> ⦃ IsTrue bo ⦄ -> bo ≡ true
propIsTrueIsJustTrue true = refl

propIfSwitch : {x y : a} -> (if true then x else y) ≡ (if false then y else x)
propIfSwitch = refl

propIfSwitchBool : {x y : a} -> (bo : Bool) -> (if bo then x else y) ≡ (if (not bo) then y else x)
propIfSwitchBool true = refl
propIfSwitchBool false = refl

propTrueOrFalseEquivTrue : (bo₁ : Bool) -> (bo₂ : Bool) -> ⦃ IsTrue bo₁ ⦄ -> (bo₁ || bo₂) ≡ true
propTrueOrFalseEquivTrue true false = refl
propTrueOrFalseEquivTrue true true = refl

propFalseOrTrueEquivTrue : (bo₁ : Bool) -> (bo₂ : Bool) -> ⦃ IsTrue bo₂ ⦄ -> (bo₁ || bo₂) ≡ true
propFalseOrTrueEquivTrue false true = refl
propFalseOrTrueEquivTrue true true = refl

propIsTrueEquivTrue : (bo : Bool) -> ⦃ IsTrue bo ⦄ -> bo ≡ true
propIsTrueEquivTrue true = refl

propAllTrueWithPropIsAllTrue : (bos₁ : List Bool) -> (bos₂ : List Bool) -> (bos₁ ≡ bos₂) -> ⦃ All IsTrue bos₁ ⦄ -> All IsTrue bos₁ ≡ All IsTrue bos₂
propAllTrueWithPropIsAllTrue [] [] refl = refl
propAllTrueWithPropIsAllTrue (bo₁ ∷ bos₁) (bo₂ ∷ bos₂) refl = refl

propImpliesProp : a -> (a ≡ b) -> b
propImpliesProp x refl = x

propIfBoolElseFalseEquivAnd : (bo₁ : Bool) -> (bo₂ : Bool) -> (if bo₁ then bo₂ else false) ≡ (bo₁ && bo₂)
propIfBoolElseFalseEquivAnd true true = refl
propIfBoolElseFalseEquivAnd true false = refl
propIfBoolElseFalseEquivAnd false true = refl
propIfBoolElseFalseEquivAnd false false = refl

postulate
  -- | Should be true
  sameNodeIsEq : (n : Int) -> (n == n) ≡ true
  sameNodeIsEq' : (n : Int) -> (v : Int) -> ⦃ IsTrue (n == v) ⦄ -> n ≡ v

  -- | Should be true but isn't true if the Eq instance is incorrectly defined. 
  sameElemIsEq : ⦃ _ : Eq a ⦄ -> (n : a) -> (n == n) ≡ true