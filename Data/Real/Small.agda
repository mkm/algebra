{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Real.Small where

open import Prelude
open import Data.Delay

data Sign : Type where
  s₋ : Sign
  s₀ : Sign
  s₊ : Sign

data ℝ : Type

data ℝ where
  real : Sign → Delay ℝ → ℝ
  shift₋ : ∀ x → real s₋ (delay (real s₊ x)) ≡ real s₀ (delay (real s₋ x))
  shift₊ : ∀ x → real s₀ (delay (real s₊ x)) ≡ real s₊ (delay (real s₋ x))

negate : ℝ → ℝ
negate′ : Delay ℝ → Delay ℝ

negate (real s₋ x) = real s₊ (negate′ x)
negate (real s₀ x) = {! !}
negate (real s₊ x) = {! !}
negate _ = {! !}

force (negate′ x) = negate (force x)

{-
primary (negate′ s₋ x) = s₊
primary (negate′ s₀ x) = s₀
primary (negate′ s₊ x) = s₋
rest (negate′ s x) = negate x

_⊕_ : ℝ → ℝ → ℝ
_⊕′_ : ℝ′ → ℝ′ → ℝ′

real x ⊕ real y = real (x ⊕′ y)
_ ⊕ _ = {! !}

x ⊕′ y = {! !}

min : ℝ
mid : ℝ
max : ℝ

min′ : ℝ′
primary min′ = s₋
rest min′ = min

min = real min′

mid′ : ℝ′
primary mid′ = s₀
rest mid′ = mid

mid = real mid′

max′ : ℝ′
primary max′ = s₊
rest max′ = max

max = real max′
-}
