{-# OPTIONS --cubical --prop #-}
module ZF where

open import Path
open import Logic
open import Sum
open import Nat

data Menge : Type

data ∀∈ (P : Menge → Type) : Menge → Type
data ∃∈ (P : Menge → Type) : Menge → Type

syntax ∀∈ (λ x → P) A = ∀[ x ∈ A ] P
syntax ∃∈ (λ x → P) A = ∃[ x ∈ A ] P

infixr 0 ∀∈ ∃∈

_⊆_ : Menge → Menge → Type

data Menge where
  ∅ : Menge
  _⋈_ : Menge → Menge → Menge
  _∪_ : Menge → Menge → Menge
  ext : ∀ {A B} → A ⊆ B → B ⊆ A → A ≡ B
  Menge-set : is-set Menge

infix 80 _⋈_ _∪_

data ∀∈ P where
  forall-⋈ : ∀ {a₁ a₂} → P a₁ → P a₂ → ∀[ a ∈ a₁ ⋈ a₂ ] P a
  forall-∪ : ∀ {A B} → ∀[ a ∈ A ] P a → ∀[ b ∈ B ] P b → ∀[ x ∈ A ∪ B ] P x

data ∃∈ P where
  exists-⋈₁ : ∀ {a₁ a₂} → P a₁ → ∃[ a ∈ a₁ ⋈ a₂ ] P a
  exists-⋈₂ : ∀ {a₁ a₂} → P a₂ → ∃[ a ∈ a₁ ⋈ a₂ ] P a
  exists-∪₁ : ∀ {A B} → ∃[ a ∈ A ] P a → ∃[ x ∈ A ∪ B ] P x
  exists-∪₂ : ∀ {A B} → ∃[ b ∈ B ] P b → ∃[ x ∈ A ∪ B ] P x

A ⊆ B = ∀[ a ∈ A ] ∃[ b ∈ B ] a ≡ b

_∈_ : Menge → Menge → Type
a ∈ A = ∃[ a′ ∈ A ] a ≡ a′

infix 50 _∈_

⟨_⟩ : Menge → Menge
⟨ a ⟩ = a ⋈ a

pair : Menge → Menge → Menge
pair a b = a ⋈ (a ⋈ b)

von-number : ℕ → Menge
von-number zero = ∅
von-number (succ n) = von-number n ⋈ ⟨ von-number n ⟩

is-inhabited : Menge → Type
is-inhabited ∅ = ♯ ⊥
is-inhabited (a₁ ⋈ a₂) = ♯ ⊤
is-inhabited (A ∪ B) = ! (is-inhabited A ⊕ is-inhabited B)
is-inhabited (ext α β i) = {!!}
is-inhabited (Menge-set a b p q i j) = {!!}

⋈-comm : ∀ a b → a ⋈ b ≡ b ⋈ a
⋈-comm a b = ext (sub a b) (sub b a)
  where
    sub : ∀ a b → a ⋈ b ⊆ b ⋈ a
    sub a b = forall-⋈ (exists-⋈₂ id) (exists-⋈₁ id)
