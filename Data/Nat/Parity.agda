{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Nat.Parity where

open import Prelude
open import Path.Comp
open import Data.Bool
open import Data.Nat

data Parity : Type where
  even : Parity
  odd : Parity

is-even : Parity → Bool
is-even even = true
is-even odd = false

odd-vs-even : odd ≢ even
odd-vs-even p = false-vs-true (ap is-even p)

succ-parity : Parity → Parity
succ-parity even = odd
succ-parity odd = even

parity : ℕ → Parity
parity zero = even
parity (succ n) = succ-parity (parity n)

+-parity : Parity → Parity → Parity
+-parity even = id
+-parity odd = succ-parity

·-parity : Parity → Parity → Parity
·-parity even _ = even
·-parity odd p = p

double-parity : ∀ p → +-parity p p ≡ even
double-parity even = refl
double-parity odd = refl

square-parity : ∀ p → ·-parity p p ≡ p
square-parity even = refl
square-parity odd = refl

succ-parity-sound : ∀ n → parity (succ n) ≡ succ-parity (parity n)
succ-parity-sound zero = refl
succ-parity-sound (succ n) = refl

+-succ-parity : ∀ p q → +-parity (succ-parity p) q ≡ succ-parity (+-parity p q)
+-succ-parity even q = refl
+-succ-parity odd even = refl
+-succ-parity odd odd = refl

+-parity-sound : ∀ m n → parity (m + n) ≡ +-parity (parity m) (parity n)
+-parity-sound zero n = refl
+-parity-sound (succ m) n =
  succ-parity-sound (m + n) ■₃
  ap succ-parity (+-parity-sound m n) ■₃
  inv (+-succ-parity (parity m) (parity n))

·-succ-parity : ∀ p q → ·-parity (succ-parity p) q ≡ +-parity (·-parity p q) q
·-succ-parity even _ = refl
·-succ-parity odd q = inv (double-parity q)

·-parity-sound : ∀ m n → parity (m · n) ≡ ·-parity (parity m) (parity n)
·-parity-sound zero n = refl
·-parity-sound (succ m) n =
  +-parity-sound (m · n) n ■
  (λ i → +-parity (·-parity-sound m n i) (parity n)) ■
  inv (·-succ-parity (parity m) (parity n))

succ-succ-parity : ∀ p → succ-parity (succ-parity p) ≡ p
succ-succ-parity even = refl
succ-succ-parity odd = refl

half : ∀ n → parity n ≡ even → ℕ
half zero _ = zero
half (succ zero) p = absurd $ odd-vs-even p
half (succ (succ n)) p = succ $ half n (inv (succ-succ-parity (parity n)) ■ p)
