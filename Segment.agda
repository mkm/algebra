{-# OPTIONS --cubical --prop #-}
module Segment where

open import Path

data Seg : Type where
  s0 : Seg
  s1 : Seg
  seg : s0 ≡ s1

_∧ₛ_ : Seg → Seg → Seg
s0 ∧ₛ y = s0
s1 ∧ₛ y = y
seg i ∧ₛ s0 = s0
seg i ∧ₛ s1 = seg i
seg i ∧ₛ seg j = seg (i ∧ j)

_∨ₛ_ : Seg → Seg → Seg
s0 ∨ₛ y = y
s1 ∨ₛ y = s1
seg i ∨ₛ s0 = seg i
seg i ∨ₛ s1 = s1
seg i ∨ₛ seg j = seg (i ∨ j)

~ₛ_ : Seg → Seg
~ₛ s0 = s1
~ₛ s1 = s0
~ₛ seg i = seg (~ i)

from-seg : ∀ {ℓ} {A : Type ℓ} → (I → A) → Seg → A
from-seg f s0 = f i0
from-seg f s1 = f i1
from-seg f (seg i) = f i

data Bound : Type where
  Is0 : Seg → Bound
  Is1 : Seg → Bound
  _∪_ : Bound → Bound → Bound
  _∩_ : Bound → Bound → Bound

data So : Bound → Type where
  is0 : So (Is0 s0)
  is1 : So (Is1 s1)
  left : ∀ {b₁ b₂} → So b₁ → So (b₁ ∪ b₂)
  right : ∀ {b₁ b₂} → So b₂ → So (b₁ ∪ b₂)
  both : ∀ {b₁ b₂} → So b₁ → So b₂ → So (b₁ ∩ b₂)

bound-one : Bound → Seg
bound-one (Is0 x) = ~ₛ x
bound-one (Is1 x) = x
bound-one (b₁ ∪ b₂) = bound-one b₁ ∨ₛ bound-one b₂
bound-one (b₁ ∩ b₂) = bound-one b₁ ∧ₛ bound-one b₂

bound-is-one : {b : Bound} → So b → So (Is1 (bound-one b))
bound-is-one is0 = is1
bound-is-one is1 = is1
bound-is-one (left p) = {!bound-is-one p!}
bound-is-one (right p) = {!!}
bound-is-one (both p₁ p₂) = {!!}

from-bound : ∀ {ℓ} {A : Type ℓ} → (I → A) → Bound → A
from-bound f b = {!!}
