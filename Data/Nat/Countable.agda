{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Nat.Countable where

open import Prelude
open import Path.Comp
open import Data.Nat
open import Data.Nat.Parity
open import Data.Truncation.Base
open import Path.Equiv

Countable : ∀ {ℓ} → Type ℓ → Type ℓ
Countable A = ∣ A ≅ ℕ ∣₀

countable-prop : ∀ {ℓ} (A : Type ℓ) → IsProp (Countable A)
countable-prop _ = collapse₀

ℕ-countable : Countable ℕ
ℕ-countable = forget₀ ≅-id

ℕ-pair : ℕ → ℕ → ℕ
ℕ-pair m n = n + half (succ (m + n) · (m + n)) p
  where
    p : parity (succ (m + n) · (m + n)) ≡ even
    p =
      parity (succ (m + n) · (m + n))
        ■⟨ ·-parity-sound (succ (m + n)) (m + n) ⟩
      ·-parity (succ-parity (parity (m + n))) (parity (m + n))
        ■⟨ ·-succ-parity (parity (m + n)) (parity (m + n)) ⟩
      +-parity (·-parity (parity (m + n)) (parity (m + n))) (parity (m + n))
        ■⟨ (λ i → +-parity (square-parity (parity (m + n)) i) (parity (m + n))) ⟩
      +-parity (parity (m + n)) (parity (m + n))
        ■⟨ double-parity (parity (m + n)) ⟩
      even
        ■⟨QED⟩
