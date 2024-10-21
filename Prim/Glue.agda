{-# OPTIONS --cubical #-}
module Prim.Glue where

open import Prim.Core
open import Prim.Interval
open import Prim.Equiv

primitive
  primGlue : ∀ {ℓ₁ ℓ₂} (B : Set ℓ₁) {φ : I}
    → (A : Partial φ (Type ℓ₂)) → (PartialP φ (λ o → A o ≅ B)) → Set ℓ₂

  prim^glue : ∀ {ℓ₁ ℓ₂} {B : Set ℓ₁} {φ : I} {A : Partial φ (Set ℓ₂)} {e : PartialP φ (λ o → A o ≅ B)}
    → PartialP φ A → B → primGlue B A e

  prim^unglue : ∀ {ℓ₁ ℓ₂} {B : Set ℓ₁} {φ : I} {A : Partial φ (Set ℓ₂)} {e : PartialP φ (λ o → A o ≅ B)}
    → primGlue B A e → B
