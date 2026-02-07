{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import HLevels

private variable
  ℓ ℓ' ℓ'' : Level

_∼_ : {A : Type ℓ} {B : A → Type ℓ'} (f g : (x : A) → B x) → Type (ℓ-max ℓ ℓ')
f ∼ g = (x : _) → f x ≡ g x
infixr 4 _∼_

∼refl : {A : Type ℓ} {B : A → Type ℓ'} {f : (x : A) → B x} → f ∼ f
∼refl x = refl

∼sym : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} → f ∼ g → g ∼ f
∼sym fg = λ x → sym (fg x)

∼trans : {A : Type ℓ} {B : A → Type ℓ'} {f g h : (x : A) → B x} → f ∼ g → g ∼ h → f ∼ h
∼trans fg gh = λ x → fg x ∙ gh x

∼LWhisk : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : A → B) {g g' : B → C} → g ∼ g' → (g ∘ f) ∼ (g' ∘ f)
∼LWhisk f gg' = λ x → gg' (f x)
∼RWhisk : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f f' : A → B} → f ∼ f' → (g : B → C) → (g ∘ f) ∼ (g ∘ f')
∼RWhisk ff' g = λ x → cong g (ff' x)

module _ {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
  hasLInv : Type (ℓ-max ℓ ℓ')
  hasLInv = Σ (B → A) (λ g → g ∘ f ∼ id)
  hasRInv : Type (ℓ-max ℓ ℓ')
  hasRInv = Σ (B → A) (λ g → f ∘ g ∼ id)
  hasQInv : Type (ℓ-max ℓ ℓ')
  hasQInv = Σ (B → A) (λ g → (g ∘ f ∼ id) × (f ∘ g ∼ id))
  isEquiv : Type (ℓ-max ℓ ℓ')
  isEquiv = hasLInv × hasRInv
  hasQInv→isEquiv : hasQInv → isEquiv
  hasQInv→isEquiv hsQI = ((fst hsQI) , fst (snd hsQI)) , (fst hsQI) , snd (snd hsQI)
  isEquiv→hasQInv : isEquiv → hasQInv
  isEquiv→hasQInv ((fba1 , gfid) ,  (fba2 , fgid)) =
    let
      fba1≡fba2 : (x : B) → (fba1 x ≡ fba2 x)
      fba1≡fba2 = λ x → cong fba1 (sym (fgid x)) ∙ gfid (fba2 x) 
    in
    (λ x → fba1 x) , (λ x → gfid x) , λ x → cong f (fba1≡fba2 x) ∙ fgid x
    
  postulate
    isPropIsEquiv : isProp isEquiv


Iso : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
Iso A B = Σ (A → B) hasQInv
_≃_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B = Σ (A → B) isEquiv
infix 4 _≃_

module _ {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) where
  equivFun : A → B
  equivFun = fst e

  invEq : B → A
  invEq = isEquiv→hasQInv equivFun (snd e) .fst

  retEq : invEq ∘ equivFun ∼ id
  retEq = isEquiv→hasQInv equivFun (snd e) .snd .fst

  secEq : equivFun ∘ invEq ∼ id
  secEq = isEquiv→hasQInv equivFun (snd e) .snd .snd
  
isoToEquiv : {A : Type ℓ} {B : Type ℓ'} → Iso A B → A ≃ B
isoToEquiv (fab , (fba , (gfid , fgid))) = fab , ((fba , (λ x → gfid x)) , fba , fgid)

idEquiv :  {A : Type ℓ} → A ≃ A
idEquiv = (λ z → z) , (((λ x → x) , (λ x → refl)) , (λ x → x) , (λ x → refl))
  
invEquiv : {A : Type ℓ} {B : Type ℓ'} → A ≃ B → B ≃ A
invEquiv (fab , ((fba1 , gfid) , (fba2 , fgid))) =
  let
    fba1≡fba2 = λ x → cong fba1 (sym (fgid x)) ∙ gfid (fba2 x)
  in
  fba2 , (fab , fgid) , (fab , (λ x → sym (fba1≡fba2 (fab x)) ∙ gfid x))
    
compEquiv : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → A ≃ B → B ≃ C → A ≃ C
compEquiv (fab , ((fba1 , gfid) , (fba2 , fgid))) (gbc , ((fcb1 , hgid) , (fcb2 , ghid))) = (λ x → gbc (fab x)) , ((λ z → fba1 (fcb1 z)) , λ x → cong fba1 (hgid (fab x)) ∙ gfid x) , (λ z → fba2 (fcb2 z)) , λ x → cong gbc (fgid (fcb2 x)) ∙ ghid x

_≃⟨_⟩_ : (A : Type ℓ) {B : Type ℓ'} {C : Type ℓ''} → (A ≃ B) → (B ≃ C) → (A ≃ C)
_ ≃⟨ f ⟩ g = compEquiv f g

_■ : (A : Type ℓ) → (A ≃ A)
_■ A = idEquiv

infixr  0 _≃⟨_⟩_
infix   1 _■

equivEq : {A : Type ℓ} {B : Type ℓ'} {e e' : A ≃ B} → equivFun e ≡ equivFun e' → e ≡ e'
{-
equivEq {ℓ} {ℓ'}{A} {B} {(fab , isEq1)} {(fab' , isEq2)} refl  = Σ≡ refl (congP ( (λ f →  Σ (Σ (B → A) (λ g → (x : A) → g (f x) ≡ x))
       (λ _ → Σ (B → A) (λ g → (x : B) → f (g x) ≡ x)))) (λ x → (invEq {!!} , {!!}) , {!!} , {!!})  refl)
-}
equivEq {ℓ} {ℓ'}{A} {B}{(fab , isEq1)} {(fab' , isEq2)} p = Σ≡ p (isPropIsEquiv fab' (subst isEquiv p isEq1) isEq2)
{-or I can do pattern matching on p-}

points≃ : (A : Type ℓ) → A ≃ (⊤ → A)
points≃ A = (λ x → λ {tt → x}) , (((λ x → x tt) , (λ x → refl)) , (λ x → x tt) , (λ x → refl))

≃⊤→isContr : {A : Type} → A ≃ ⊤ → isContr A
≃⊤→isContr e = invEq e tt , λ y → cong (invEq e) refl ∙ retEq e y 

not : Bool → Bool
not true = false
not false = true

not≃ : Bool ≃ Bool
not≃ = not , (((λ z → not z) , λ {true → refl ; false → refl}) , (λ z → not z) , λ {true → refl ; false → refl})

×≡Equiv : {A : Type ℓ} {B : Type ℓ} {x x' : A} {y y' : B} → ((x , y) ≡ (x' , y')) ≃ (x ≡ x') × (y ≡ y')
×≡Equiv {ℓ} {A} {B} {x} {x'} {y} {y'} = ≡× , ((λ x₁ → ×≡ (fst x₁) (snd x₁)) , λ x₁ → ≡×≡ (x , y) (x' , y') x₁) , (λ x₁ → ×≡ (fst x₁) (snd x₁)) , λ {(refl , refl) → refl}

Σ≡Equiv : {A : Type ℓ} (B : A → Type ℓ') {x x' : A} {y : B x} {y' : B x'} → ((x , y) ≡ (x' , y')) ≃ Σ (x ≡ x') (λ p → PathOver B p y y')
Σ≡Equiv B {x} {x'} {y} {y'} = ( λ {refl → (refl , refl)}) , ((λ x₁ → Σ≡ (fst x₁) (snd x₁)) , λ {refl → refl}) , (λ x₁ → Σ≡ (fst x₁) (snd x₁)) , λ {(refl , refl) → refl}
{-
Σ≡Equiv' : {A : Type ℓ} (B : A → Type ℓ') {x x' : A} {y : B x} {y' : B x'} → ((x , y) ≡ (x' , y')) ≃ Σ (x ≡ x') (λ p → PathOver B p y y')
Σ≡Equiv' B {x} {x'} {y} {y'} = (λ x₁ → cong fst x₁ , J (λ y₁ eq → PathOver B {!!} y {!!}) {!!} {!!}) , ((λ x₁ → Σ≡ (fst x₁) (snd x₁)) , {!!}) , (λ x₁ → Σ≡ (fst x₁) (snd x₁)) , {!!}
-}
