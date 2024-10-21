{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Rational where

open import Prelude
open import Path.Comp
import Data.Nat as N
open import Data.SuccNat
  renaming (_+_ to _+″_; _·_ to _·″_)
open import Data.Int
  renaming (_+_ to _+′_; _·_ to _·′_; succ to succ′)
open import Data.Truncation

is-quot : ℤ → ℤ → ℕ₊ → ℕ₊ → Type
is-quot n₁ n₂ d₁ d₂ = n₁ ·′ pos (as-succ d₂) ≡ n₂ ·′ pos (as-succ d₁)

data ℚ : Type where
  _/_ : ℤ → ℕ₊ → ℚ
  quot : ∀ n₁ n₂ d₁ d₂ → is-quot n₁ n₂ d₁ d₂ → n₁ / d₁ ≡ n₂ / d₂
  ℚ-set : IsSet ℚ

from-ℤ : ℤ → ℚ
from-ℤ n = n / succ₊ zero

ℚ-rec : ∀ {ℓ} {A : Type ℓ} → IsSet A → (f : ℤ → ℕ₊ → A) → (∀ n₁ n₂ d₁ d₂ → is-quot n₁ n₂ d₁ d₂ → f n₁ d₁ ≡ f n₂ d₂) → ℚ → A
ℚ-rec A-set f p (n / d) = f n d
ℚ-rec A-set f p (quot n₁ n₂ d₁ d₂ q i) = p n₁ n₂ d₁ d₂ q i
ℚ-rec A-set f p (ℚ-set x y q r i j) =
  A-set (ℚ-rec A-set f p x) (ℚ-rec A-set f p y) (λ j → ℚ-rec A-set f p (q j)) (λ j → ℚ-rec A-set f p (r j)) i j

recip : ℚ → ℚ
recip = ℚ-rec ℚ-set
  (ℤ-rec
    (λ n d → neg (as-succ d) / succ₊ n)
    (λ _ → neg zero / succ₊ zero)
    (λ n d → pos (as-succ d) / succ₊ n))
  (ℤ-ind
    (λ n₁ → ℤ-ind
      (λ n₂ d₁ d₂ p → quot (neg (as-succ d₁)) (neg (as-succ d₂)) (succ₊ n₁) (succ₊ n₂) {! !})
      {! !}
      {! !})
    {! !}
    {! !})

{-
  (λ where
    (neg zero) d → neg zero / succ₊ zero
    (neg (succ n)) d → neg (as-succ d) / succ₊ n
    (pos zero) d → pos zero / succ₊ zero
    (pos (succ n)) d → pos (as-succ d) / succ₊ n
    (zero i) d → zero i / succ₊ zero)
  λ where
    (neg zero) (neg zero) d₁ d₂ p i → neg zero / succ₊ zero
    (neg zero) (neg (succ n₂)) d₁ d₂ p → absurd (N.zero-vs-succ (neg-inj p ■ N.+-succ _ _))
    (neg zero) (pos zero) d₁ d₂ p i → zero i / succ₊ zero
    (neg zero) (pos (succ n)) d₁ d₂ p → absurd (N.zero-vs-succ (zero-pos-inj i0 p ■ N.+-succ _ _))
    (neg zero) (zero j) d₁ d₂ p i → zero (i ∧ j) / succ₊ zero
    (neg (succ n₁)) (neg zero) d₁ d₂ p i → {! !}
    (neg (succ n₁)) n₂ d₁ d₂ p i → {! !}
    n₁ n₂ d₁ d₂ p i → {! !}
    -}
{-
recip (neg zero / d) = neg zero / succ₊ zero
recip (neg (succ n) / d) = neg (as-succ d) / succ₊ n
recip (pos zero / d) = pos zero / succ₊ zero
recip (pos (succ n) / d) = pos (as-succ d) / succ₊ n
recip (zero i / d) = zero i / succ₊ zero
recip (quot n₁ n₂ d₁ d₂ p i) = {! !}
recip (ℚ-set x y p q i j) = {! !}
-}

_·_ : ℚ → ℚ → ℚ
(n₁ / d₁) · (n₂ / d₂) = (n₁ ·′ n₂) / (d₁ ·″ d₂)
(n₁ / d₁) · quot n₂ n₂′ d₂ d₂′ p i = quot (n₁ ·′ n₂) (n₁ ·′ n₂′) (d₁ ·″ d₂) (d₁ ·″ d₂′) {! !} i
_ · _ = {! !}
