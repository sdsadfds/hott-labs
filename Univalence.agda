{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import HLevels
open import Equivalence

private variable
  ℓ ℓ' : Level

pathToEquiv : {A B : Type ℓ} → A ≡ B → A ≃ B
pathToEquiv {ℓ} {A} {B} p = (λ x → transport p x) , ((λ x → transport (sym p) x) , (λ x → J (λ B₁ eq → transport (sym eq) (transport eq x) ≡ id x) refl p)) , ((λ x → transport (sym p) x) , λ x → cong (λ x₁ → transport x₁ (transport (sym p) x)) (symInvo p) ∙ J (λ A₁ eq →  transport (sym eq) (transport eq x) ≡ id x) refl (sym p))

pathToEquivTest : {A B : Type ℓ} (p : A ≡ B) → equivFun (pathToEquiv p) ≡ transport p
pathToEquivTest p = refl

postulate
  -- Univalence!
  isEquivPathToEquiv : {A B : Type ℓ} → isEquiv (pathToEquiv {A = A} {B = B})

univalence : {A B : Type ℓ} → (A ≡ B) ≃ (A ≃ B)
univalence = pathToEquiv , isEquivPathToEquiv

ua : {A B : Type ℓ} → A ≃ B → A ≡ B
ua e = invEq univalence e

uaβ : {A B : Type ℓ} (e : A ≃ B) → transport (ua e) ≡ equivFun e
uaβ e = sym (pathToEquivTest (ua e)) ∙ cong equivFun (secEq univalence e)

uaη : {A B : Type ℓ} (p : A ≡ B) → ua (pathToEquiv p) ≡ p
uaη p = retEq univalence p

uaIdEquiv : {A : Type ℓ} → ua (idEquiv {A = A}) ≡ refl
uaIdEquiv {A = A} = uaη refl

isContr≃≡⊤ : {A : Type} → isContr A ≃ (A ≡ ⊤)
isContr≃≡⊤ = (λ x → ua ((λ _ → tt) , (((λ _ → fst x) , (snd x)) , ((λ _ → fst x) , λ {tt → refl})))) , ((λ x → J (λ y eq → isContr y) isContr⊤ (sym x)) , λ x → isPropIsContr (J (λ y eq → isContr y) isContr⊤
      (sym
       (ua
        ((λ _ → tt) ,
         ((λ _ → fst x) , snd x) , (λ _ → fst x) , (λ x₁ → refl))))) x) , (λ x → J (λ y eq → isContr y) isContr⊤ (sym x)) , λ {refl → uaIdEquiv}

is¬≃≡⊥ : {A : Type} → (¬ A) ≃ (A ≡ ⊥)
is¬≃≡⊥ =
  let
    help1 =  λ x → (x , (((λ ()) , (λ x₁ → ⊥-rec (x x₁))) , (λ ()) , (λ ())))
  in
  (ua ∘ help1) , ((fst ∘ (equivFun univalence)) , λ x → cong fst (secEq univalence (help1 x))) , (fst ∘ (equivFun univalence)) , λ x → cong ua (equivEq refl) ∙ retEq univalence x

≃ind : (P : {A B : Type ℓ} → (A ≃ B) → Type ℓ') →
       ({A : Type ℓ} → P (idEquiv {A = A})) →
       {A B : Type ℓ} (e : A ≃ B) → P e
≃ind P q e with (ua e)
... | refl = {!q!}
