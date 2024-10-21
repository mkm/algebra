{-# OPTIONS --cubical --prop #-}
module Logic where

open import Path
open import String
open import Show

data ⊥ : Prop where

record ⊤ : Prop where
  constructor top

¬_ : ∀ {ℓ} → Type ℓ → Prop ℓ
¬_ A = A → ⊥

infixr 20 ¬_

¬¬_ : Type → Prop
¬¬ A = ¬ A → ⊥

infixr 20 ¬¬_

_≢_ : ∀ {ℓ} {A : Type ℓ} → A → A → Prop ℓ
x ≢ y = ¬ (x ≡ y)

infix 4 _≢_

⊥-elim : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
⊥-elim ()

data ♭_ {ℓ} (A : Type ℓ) : Prop ℓ where
  squash : A → ♭ A

infix 1 ♭_

squash-contra : {A : Type} → ♭ A → ¬¬ A
squash-contra (squash x) contra = contra x

record ♯_ {ℓ} (A : Prop ℓ) : Type ℓ where
  constructor lift
  field
    proof : A

open ♯_ public

infix 1 ♯_

!_ : ∀ {ℓ} → Type ℓ → Type ℓ
!_ A = ♯ ♭ A

infix 1 !_

∣_∣ : ∀ {ℓ} {A : Type ℓ} → A → ! A
∣ x ∣ = lift (squash x)

squashf : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → ♭ A → ♭ B
squashf f (squash x) = squash (f x)

squashf₂ : ∀ {ℓ} {A B C : Type ℓ} → (A → B → C) → ♭ A → ♭ B → ♭ C
squashf₂ f (squash x) (squash y) = squash (f x y)

liftf : ∀ {ℓ₁ ℓ₂} {A : Prop ℓ₁} {B : A → Prop ℓ₂} → ((x : A) → B x) → (x : ♯ A) → ♯ B (proof x)
liftf f x = lift (f (proof x))

liftf₂ : ∀ {ℓ} {A B C : Prop ℓ} → (A → B → C) → ♯ A → ♯ B → ♯ C
liftf₂ f x y = lift (f (proof x) (proof y))

{-
♯-prop : ∀ {ℓ} {A : Prop ℓ} → is-prop (♯ A)
♯-prop x y = id
-}

∣_∣₁ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → ! A → ! B
∣ f ∣₁ = liftf (squashf f)

∣_∣₂ : ∀ {ℓ} {A B C : Type ℓ} → (A → B → C) → ! A → ! B → ! C
∣ f ∣₂ = liftf₂ (squashf₂ f)

record ∃ {ℓ} {A : Type ℓ} (B : A → Prop ℓ) : Type ℓ where
  field
    witness : A
    indeed : B witness

open ∃ public

syntax ∃ (λ x → B) = x ⇒ B

record _⇔_ (P Q : Prop) : Prop where
  field
    ltr : P → Q
    rtl : Q → P

open _⇔_ public

infix 5 _⇔_

postulate
  bisim-path : {P Q : Prop} → P ⇔ Q → P ≡ Q

instance
  show-♯ : ∀ {A} → Show (♯ A)
  Show.show show-♯ _ = "!"
