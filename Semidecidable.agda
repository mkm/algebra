{-# OPTIONS --cubical --prop --guardedness #-}
module Semidecidable where

open import Path
open import Nat
open import Sum
open import Product

record Sec° {ℓ} (A : Type ℓ) : Type ℓ
data Sec {ℓ} (A : Type ℓ) : Type ℓ
record _≈_ {ℓ} {A : Type ℓ} (d° e° : Sec° A) : Type ℓ

record Sec° A where
  coinductive
  constructor delay
  field
    force : Sec A

open Sec° public

record _≈_ d° e° where
  coinductive
  field
    force-≈ : force d° ≡ force e°

open _≈_ public

data Sec A where
  yes : A → Sec A
  ponder : Sec° A → Sec A

ponders : ∀ {ℓ} {A : Type ℓ} → ℕ → Sec A → Sec A
ponders zero d = d
ponders (succ n) d = ponder (delay (ponders n d))

force′ : ∀ {ℓ} {A : Type ℓ} → Sec A → Sec A
force′ (yes a) = yes a
force′ (ponder d°) = force d°

forces : ∀ {ℓ} {A : Type ℓ} → ℕ → Sec A → Sec A
forces zero d = d
forces (succ n) d = force′ (forces n d)

no° : ∀ {ℓ} {A : Type ℓ} → Sec° A
no : ∀ {ℓ} {A : Type ℓ} → Sec A

force no° = no
no = ponder no°

map° : ∀ {ℓ} {A B : Type ℓ} → (A → B) → Sec° A → Sec° B
map : ∀ {ℓ} {A B : Type ℓ} → (A → B) → Sec A → Sec B

force (map° f d) = map f (force d)

map f (yes a) = yes (f a)
map f (ponder d°) = ponder (map° f d°)

_||°_ : {A B : Type} → Sec° A → Sec° B → Sec° (A ⊕ B)
_||_ : {A B : Type} → Sec A → Sec B → Sec (A ⊕ B)

force (d° ||° e°) = force d° || force e°

yes a || e = yes (lft a)
ponder d° || yes a = yes (rgt a)
ponder d° || ponder e° = ponder (d° ||° e°)

_&&°_ : {A B : Type} → Sec° A → Sec B → Sec° (A × B)
_&&_ : {A B : Type} → Sec A → Sec B → Sec (A × B)

force (d°₁ &&° d₂) = force d°₁ && d₂

yes a && e = map (λ b → a , b) e
ponder d° && e = ponder (d° &&° e)
