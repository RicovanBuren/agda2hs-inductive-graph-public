-- https://plfa.github.io/Equality/
module Proofs.Proof where

open import Agda.Builtin.Equality


subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

-- symmetry of equality
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- transitivity of equality
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- congruence of equality
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

-- Congruence of functions with two arguments is similar:
cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B} → u ≡ x → v ≡ y → f u v ≡ f x y
cong₂ f refl refl  =  refl

-- Equality is also a congruence in the function position of an application. If two functions are equal, then applying them to the same term yields equal terms:
cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl

_end : {A : Set} → (x : A) → x ≡ x
_end = _∎

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=<_>_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
_=<_>_ = _=⟨_⟩_

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

_=<>_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
_=<>_ = _=⟨⟩_

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

infix   1  begin_
infix   3  _∎
infix   3  _end
infixr  2  _=⟨_⟩_
infixr  2  _=⟨⟩_
infixr  2  _=<_>_
infixr  2  _=<>_
