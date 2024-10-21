{-# OPTIONS --cubical --erasure #-}
module Control.Functor where

open import Prelude

record Functor (F : ∀ {ℓ} → Type ℓ → Type ℓ) : Typeω where
  field
    map : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → F A → F B
    map-id : ∀ {ℓ} {A : Type ℓ} → map {A = A} id ≡ id
    map-∘ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : B → C) (g : A → B) → map (f ∘ g) ≡ map f ∘ map g

open Functor ⦃ … ⦄ public 
