{-# OPTIONS --cubical --erasure #-}
module Relation.PartialOrder where

open import Prelude
open import Path.Comp

record IsOrd {ℓ ℓ′} {A : Type ℓ} (_≤_ : A → A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  field
    ≤-refl : ∀ {x} → x ≤ x
    ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y

open IsOrd ⦃ … ⦄ public

eq-is-ord : ∀ {ℓ} {A : Type ℓ} → IsOrd {A = A} _≡_
≤-refl ⦃ eq-is-ord ⦄ = refl
≤-trans ⦃ eq-is-ord ⦄ = _■_
≤-antisym ⦃ eq-is-ord ⦄ p _ = p
