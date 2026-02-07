open import Prelude

comm× : {A B : Type} → A × B → B × A
comm× (a , b) = b , a

comm×-involutive : {A B : Type} (a : A) (b : B) → comm× (comm× (a , b)) ≡ (a , b)
comm×-involutive a b = refl

assoc× : {A B C : Type} → (A × B) × C → A × (B × C)
assoc× ((a , b), c) = (a , (b , c))

comm⊎ : {A B : Type} → A ⊎ B → B ⊎ A
comm⊎ (inl a) = inr a
comm⊎ (inr b) = inl b

comm⊎-involutive : {A B : Type} (l : A ⊎ B) → comm⊎ (comm⊎ l) ≡ l 
comm⊎-involutive (inl a) = refl
comm⊎-involutive (inr b) = refl

dist⊎ : {A B C : Type} → A × (B ⊎ C) → (A × B) ⊎ (A × C)
dist⊎ (a , inl b) = inl (a , b)
dist⊎ (a , inr c) = inr (a , c)

curry1 : {A B C : Type} → (A × B → C) → (A → B → C)
curry1 = λ f a b → f (a , b)
curry2 : {A B C : Type} → (A → B → C) → (A × B → C)
curry2 = λ g (a , b) → g a b

currying : {A B C : Type} → (A × B → C) ↔ (A → B → C)
currying = (curry1 , curry2)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

+-unitl : (n : ℕ) → zero + n ≡ n
+-unitl zero = refl
+-unitl (suc n) = refl

cong : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

+-unitr : (n : ℕ) → n + zero ≡ n
+-unitr zero = refl
+-unitr (suc n) = cong suc (+-unitr n) 

+-assoc : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
+-assoc zero zero o = refl
+-assoc zero (suc n) o = refl
+-assoc (suc m) zero o = step-≡ (suc ((m + zero) + o)) (cong suc (+-assoc m zero o)) refl
+-assoc (suc m) (suc n) o = step-≡ (suc ((m + suc n) + o)) (cong suc (+-assoc m (suc n) o)) refl

sym : {A : Type} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

+-suc : (m n : ℕ) → m + (suc n) ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero n = trans (+-unitl n) (sym (+-unitr n))
+-comm (suc m) n = trans (cong suc (+-comm m  n))  (sym (+-suc n m))

pred-suc : (n : ℕ) → pred (suc n) ≡ n
pred-suc n = refl

suc-pred : (n : ℕ) → ¬ (n ≡ zero) → suc (pred n) ≡ n
suc-pred zero neq = ⊥-rec (neq refl)
suc-pred (suc n) neq = refl

zero-suc : (n : ℕ) → ¬ (zero ≡ suc n)
zero-suc zero = λ ()
zero-suc (suc n) = λ ()

suc-inj : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj {zero} {zero} f = refl
suc-inj {suc m} {zero} ()
suc-inj {zero} {suc n} ()
suc-inj {suc m} {suc n} f = cong pred f

nat-eq-dec : (m n : ℕ) → (m ≡ n) ⊎ ¬ (m ≡ n)
nat-eq-dec zero (suc n) = inr (zero-suc n)
nat-eq-dec zero zero = inl refl
nat-eq-dec (suc m) zero = inr (λ f → zero-suc m (sym f))
nat-eq-dec (suc m) (suc n) with nat-eq-dec m n
... | inl p = inl (cong suc p)
... | inr q = inr (λ x → q (suc-inj x))

div2 : (n : ℕ) → Σ ℕ (λ q → q + q ≡ n ⊎ suc (q + q) ≡ n)
div2 zero = (0 , inl refl)
div2 (suc n) with div2 n
... | (q , inl p) = (q , inr (cong suc p))
... | (r , inr s) = suc r , inl (cong suc (trans (+-comm r (suc r)) s))

subst : {A : Type} (P : A → Type) {x y : A} → x ≡ y → P x → P y
subst f refl px = px

data Even : ℕ → Type where
  evenZero : Even zero
  evenSuc  : {n : ℕ} → Even n → Even (suc (suc n))

double-even : (n : ℕ) → Even (n + n)
double-even zero = evenZero
double-even (suc n) = subst (λ x → Even x) (cong suc (+-comm ((suc n)) n)) (evenSuc (double-even n))

rec⊎ : {A B C : Type} → (A → C) → (B → C) → A ⊎ B → C
rec⊎ f g (inl a) = f a
rec⊎ f g (inr b) = g b

elim⊎ : {A B : Type} (C : A ⊎ B → Type) → ((x : A) → C (inl x)) → ((x : B) → C (inr x)) → (x : A ⊎ B) → C x
elim⊎ f g h (inl a) = g a
elim⊎ f g h (inr b) = h b

comp⊎l : {A B : Type} (C : A ⊎ B → Type) (f : (x : A) → C (inl x)) (g : (x : B) → C (inr x)) (x : A) → elim⊎ C f g (inl x) ≡ f x
comp⊎l c f g x = refl

comp⊎r : {A B : Type} (C : A ⊎ B → Type) (f : (x : A) → C (inl x)) (g : (x : B) → C (inr x)) (x : B) → elim⊎ C f g (inr x) ≡ g x
comp⊎r c f g x = refl

uniq⊎ : {A B : Type} (x : A ⊎ B) → elim⊎ (λ _ → A ⊎ B) inl inr x ≡ x
uniq⊎ (inl a) = refl
uniq⊎ (inr b) = refl

elim× : {A B : Type} (C : A × B → Type) (f : (a : A) → (b : B) → C (a , b)) → (x : A × B) → C x
elim× c f (a , b) = f a b
