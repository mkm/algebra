{-# OPTIONS --cubical #-}
module Algebra.Category where

open import Prelude renaming (id to id′; _∘_ to _∘′_)
open import Path.Comp
open import Path.Equiv

record Category ℓₒ ℓₕ : Type (lsuc (ℓₒ ⊔ ℓₕ)) where
  field
    Obj : Type ℓₒ
    _⇒_ : Obj → Obj → Type ℓₕ
    id : ∀ A → A ⇒ A
    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
    ∘-id₁ : ∀ {A B} (f : A ⇒ B) → id B ∘ f ≡ f
    ∘-id₂ : ∀ {A B} (f : A ⇒ B) → f ∘ id A ≡ f
    ∘-assoc : ∀ {A B C D} (f : C ⇒ D) (g : B ⇒ C) (h : A ⇒ B) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
    iso-path : ∀ {A B} (f : A ⇒ B) (g : B ⇒ A) → g ∘ f ≡ id A → f ∘ g ≡ id B → A ≡ B

  infix 50 _∘_

record Functor {ℓₒ₁ ℓₒ₂ ℓₕ₁ ℓₕ₂} (𝒞 : Category ℓₒ₁ ℓₕ₁) (𝒟 : Category ℓₒ₂ ℓₕ₂) : Type (ℓₒ₁ ⊔ ℓₒ₂ ⊔ ℓₕ₁ ⊔ ℓₕ₂) where
  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟

  field
    atₒ : 𝒞.Obj → 𝒟.Obj
    atₕ : ∀ {A B} → A 𝒞.⇒ B → atₒ A 𝒟.⇒ atₒ B
    at-id : ∀ A → atₕ (𝒞.id A) ≡ 𝒟.id (atₒ A)
    at-∘ : ∀ {A B C} (f : B 𝒞.⇒ C) (g : A 𝒞.⇒ B) → atₕ (f 𝒞.∘ g) ≡ atₕ f 𝒟.∘ atₕ g

module _ {ℓₒ ℓₕ} (𝒞 : Category ℓₒ ℓₕ) where
  open Category 𝒞
  open Functor

  id-functor : Functor 𝒞 𝒞
  atₒ id-functor = id′
  atₕ id-functor = id′
  at-id id-functor _ = refl
  at-∘ id-functor _ _ = refl

module _ {ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₕ₁ ℓₕ₂ ℓₕ₃} {𝒞 : Category ℓₒ₁ ℓₕ₁} {𝒟 : Category ℓₒ₂ ℓₕ₂} {ℰ : Category ℓₒ₃ ℓₕ₃} (α : Functor 𝒟 ℰ) (β : Functor 𝒞 𝒟) where
  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module ℰ = Category ℰ
    module α = Functor α
    module β = Functor β
  open Functor

  ∘-functor : Functor 𝒞 ℰ
  atₒ ∘-functor = α.atₒ ∘′ β.atₒ
  atₕ ∘-functor = α.atₕ ∘′ β.atₕ
  at-id ∘-functor A = ap α.atₕ (β.at-id A) ■ α.at-id (β.atₒ A)
  at-∘ ∘-functor f g = ap α.atₕ (β.at-∘ f g) ■ α.at-∘ (β.atₕ f) (β.atₕ g)

module _ where
  open Category
  open Functor
  
  cat-cat : ∀ ℓₒ ℓₕ → Category (lsuc (ℓₒ ⊔ ℓₕ)) (ℓₒ ⊔ ℓₕ)
  Obj (cat-cat ℓₒ ℓₕ) = Category ℓₒ ℓₕ
  _⇒_ (cat-cat ℓₒ ℓₕ) 𝒞 𝒟 = Functor 𝒞 𝒟
  id (cat-cat ℓₒ ℓₕ) = id-functor
  _∘_ (cat-cat ℓₒ ℓₕ) = ∘-functor
  ∘-id₁ (cat-cat ℓₒ ℓₕ) {B = 𝒞} β i =
    λ where
      .atₒ → β.atₒ
      .atₕ → β.atₕ
      .at-id A → ■-refl₂ (β.at-id A) i
      .at-∘ f g → ■-refl₂ (β.at-∘ f g) i
    where
      module β = Functor β
  ∘-id₂ (cat-cat ℓₒ ℓₕ) α i =
    λ where
      .atₒ → α.atₒ
      .atₕ → α.atₕ
      .at-id A → ■-refl₁ (α.at-id A) i
      .at-∘ f g → ■-refl₁ (α.at-∘ f g) i
    where
      module α = Functor α
  ∘-assoc (cat-cat ℓₒ ℓₕ) α β γ i =
    λ where
      .atₒ → α.atₒ ∘′ β.atₒ ∘′ γ.atₒ
      .atₕ → α.atₕ ∘′ β.atₕ ∘′ γ.atₕ
      .at-id A → i ►
        (ap α.atₕ ∘′ ap β.atₕ ∘′ γ.at-id $ A) ■ ((ap α.atₕ ∘′ β.at-id ∘′ γ.atₒ $ A) ■ (α.at-id ∘′ β.atₒ ∘′ γ.atₒ $ A)) ■⟨ inv $ ■-assoc (ap α.atₕ ∘′ ap β.atₕ ∘′ γ.at-id $ A) (ap α.atₕ ∘′ β.at-id ∘′ γ.atₒ $ A) (α.at-id ∘′ β.atₒ ∘′ γ.atₒ $ A) ⟩
        ((ap α.atₕ ∘′ ap β.atₕ ∘′ γ.at-id $ A) ■ (ap α.atₕ ∘′ β.at-id ∘′ γ.atₒ $ A)) ■ (α.at-id ∘′ β.atₒ ∘′ γ.atₒ $ A) ■⟨ (λ i → ap-■ α.atₕ (ap β.atₕ ∘′ γ.at-id $ A) (β.at-id ∘′ γ.atₒ $ A) (~ i) ■ (α.at-id ∘′ β.atₒ ∘′ γ.atₒ $ A) ) ⟩
        (ap α.atₕ $ (ap β.atₕ ∘′ γ.at-id $ A) ■ (β.at-id ∘′ γ.atₒ $ A)) ■ (α.at-id ∘′ β.atₒ ∘′ γ.atₒ $ A) ■⟨QED⟩
      .at-∘ f g → {!!}
    where
      module α = Functor α
      module β = Functor β
      module γ = Functor γ
  iso-path (cat-cat ℓₒ ℓₕ) {A = 𝒞} {B = 𝒟} α β p q i =
    λ where
      .Obj → Objᵢ i
      ._⇒_ → Homᵢ i
      .id → {!!}
      ._∘_ → {!!}
      .∘-id₁ → {!!}
      .∘-id₂ → {!!}
      .∘-assoc → {!!}
      .iso-path → {!!}
    where
      module 𝒞 = Category 𝒞
      module 𝒟 = Category 𝒟
      module α = Functor α
      module β = Functor β

      Objᵢ : 𝒞.Obj ≡ 𝒟.Obj
      Objᵢ = equiv-path λ where
        .fun → α.atₒ
        .is-equiv .linv → β.atₒ
        .is-equiv .rinv → β.atₒ
        .is-equiv .is-linv → λ i → Functor.atₒ (p i)
        .is-equiv .is-rinv → λ i → Functor.atₒ (q i)

      Homᵢ : Path (λ i → Objᵢ i → Objᵢ i → Type ℓₕ) 𝒞._⇒_ 𝒟._⇒_
      Homᵢ i A B = i ► equiv-path λ where
        .fun → {!!}
        .is-equiv → {!!}
