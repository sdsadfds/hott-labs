{-# OPTIONS --without-K #-}

open import Prelude

private variable
  ℓ ℓ' : Level

postulate
  funExt : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g

open import Path

postulate
  funExtη : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} (p : f ≡ g) → funExt (happly p) ≡ p
  funExtβ : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} (p : (x : A) → f x ≡ g x) → happly (funExt p) ≡ p
