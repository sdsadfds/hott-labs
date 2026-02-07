{-# OPTIONS --without-K #-}

open import Prelude

private variable
  ℓ ℓ' : Level

postulate
  funExt : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g

open import Path

happly' :
  {A : Type ℓ} {B : A → Type ℓ'}
  {f g : (x : A) → B x} →
  f ≡ g → (x : A) → f x ≡ g x

happly' refl x = refl
postulate
  funExtη : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} (p : f ≡ g) → funExt (happly' p) ≡ p
  funExtβ : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} (p : (x : A) → f x ≡ g x) → happly' (funExt p) ≡ p
