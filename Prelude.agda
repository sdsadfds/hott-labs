{-# OPTIONS --without-K #-}

---
--- Survival kit for a standard library
---

--- Note: the main use of BUILTIN below is to ensure that η-conversion is implicit. Those require types such as Σ to be defined as records and not as plain inductive types.

open import Agda.Primitive public using (Level) renaming (Set to Type ; lzero to ℓ-zero ; lsuc to ℓ-suc ; _⊔_ to ℓ-max)

private variable
  ℓ ℓ' ℓ'' : Level

---
--- Basic types
---

data ⊥ : Type ℓ-zero where

⊥-rec : {A : Type ℓ} → ⊥ → A
⊥-rec ()

record ⊤ : Type ℓ-zero where
  instance constructor tt

{-# BUILTIN UNIT ⊤ #-}

-- Booleans
data Bool : Type ℓ-zero where
  false : Bool
  true  : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}

if_then_else_ : {A : Type ℓ} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

-- Natural numbers
data ℕ : Type where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- Negation
infix 3 ¬_
¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

---
--- Coproducts / sum
---

data _⊎_ (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

infixr 1 _⊎_

-- Allow for alternative notation
_⊔_ = _⊎_
infixr 1 _⊔_

---
--- Σ-types
---

record Σ {ℓ ℓ' : Level} (A : Type ℓ) (B : A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

{-# BUILTIN SIGMA Σ #-}

-- Products
infixr 5 _×_
_×_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A × B = Σ A (λ _ → B)

infix 4 _↔_
_↔_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ↔ B = (A → B) × (B → A)

---
--- Universe lifting
---

record Lift {ℓ' ℓ} (A : Type ℓ) : Type (ℓ-max ℓ ℓ') where
  constructor lift
  field
    lower : A

open Lift public

---
--- Identity paths (with definitional J).
---

infix 4 _≡_
data _≡_ {ℓ} {A : Type ℓ} (x : A) : (y : A) → Type ℓ where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- Chains of equational reasoning
module _ {A : Type ℓ} where
  infixr 2 step-≡ _≡⟨⟩_
  infix  3 _∎

  step-≡ : (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ p refl = p

  syntax step-≡ x y p = x ≡⟨ p ⟩ y

  _≡⟨⟩_ : (x : A) {y : A} → x ≡ y → x ≡ y
  _ ≡⟨⟩ p = p

  _∎ : (x : A) → x ≡ x
  _ ∎ = refl

infix 4 _≢_
_≢_ : {A : Type ℓ} {x y : A} (p q : x ≡ y) → Type ℓ
p ≢ q = ¬ (p ≡ q)

---
--- Functions
---

-- Identity function
id : {A : Type ℓ} → A → A
id x = x

-- Composite
infixr 9 _∘_
_∘_ : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''} (g : {a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)
{-# INLINE _∘_ #-}
