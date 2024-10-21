{-# OPTIONS --cubical --erasure #-}
module Data.Truncation.Equiv where

open import Prelude
open import Path.Equiv
open import Control.Monad
open import Data.Truncation

_≅₀_ : ∀ {ℓ ℓ′} → Type ℓ → Type ℓ′ → Type (ℓ ⊔ ℓ′)
A ≅₀ B = ∣ A ≅ B ∣₀

≅₀-id : ∀ {ℓ} {A : Type ℓ} → A ≅₀ A
≅₀-id = forget₀ ≅-id

_≅₀-∘_ : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} → A ≅₀ B → B ≅₀ C → A ≅₀ C
α ≅₀-∘ β = ⦇ α ≅-∘ β ⦈
