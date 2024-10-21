{-# OPTIONS --cubical --prop #-}
module Sigma where

open import Prelude
open import Path

record Σ {ℓ₁} {ℓ₂} (A : Type ℓ₁) (B : A → Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
