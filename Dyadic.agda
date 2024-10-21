{-# OPTIONS --cubical --prop #-}
module Dyadic where

open import Path
open import Decidable
open import Nat using (ℕ)
import Nat as N
open import Int using (ℤ; pos; neg)
import Int as Z

data ℚ₂ : Type where
  _/2^_ : (n : ℤ) (d : ℕ) → ℚ₂
  shift : ∀ n d → (pos 2 Z.· n) /2^ ℕ.succ d ≡ n /2^ d

infix 60 _/2^_

dec-eq : (x y : ℚ₂) → Dec (x ≡ y)
dec-eq (n₁ /2^ d₁) (n₂ /2^ d₂) = {!Z.dec-eq (n₁ Z.· pos (N.2^ d₂)) (n₂ Z.· pos (N.2^ d₁))!}
dec-eq (n₁ /2^ d₁) (shift n₂ d₂ j) = {!!}
dec-eq (shift n d i) y = {!!}

ℚ₂-set : is-set ℚ₂
ℚ₂-set = dec-eq-set dec-eq

_·_ : ℚ₂ → ℚ₂ → ℚ₂
(n₁ /2^ d₁) · (n₂ /2^ d₂) = (n₁ Z.· n₂) /2^ (d₁ N.+ d₂)
(n₁ /2^ d₁) · shift n₂ d₂ j = {!!}
-- (n₁ Int.· pos 2 Int.· n₂) /2^ (d₁ Nat.+ ℕ.succ d₂)
-- (n₁ Int.· n₂) /2^ (d₁ Nat.+ d₂)
shift n₁ d₁ i · (n₂ /2^ d₂) = {!!}
shift n₁ d₁ i · shift n₂ d₂ j = {!!}

infixr 60 _·_
