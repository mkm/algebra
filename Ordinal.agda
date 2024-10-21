{-# OPTIONS --cubical --prop --type-in-type #-}
module Ordinal where

open import Path
open import Logic
open import Nat using (ℕ)
import Nat as N

data Ω : Set

_≤_ : Ω → Ω → Prop
_<_ : Ω → Ω → Prop

≤-≤ : ∀ α β γ → α ≤ β → β ≤ γ → α ≤ γ

data Ω where
  zero : Ω
  succ : Ω → Ω
  lim : (ℕ → Ω) → Ω
  equiv : ∀ {α β} → ♯ (α ≤ β) → ♯ (β ≤ α) → α ≡ β
  Ω-set : is-set Ω

into-Prop : (P : Ω → Prop) → P zero → (∀ α → P α → P (succ α)) → (∀ α⁻ → (∀ n → P (α⁻ n)) → P (lim α⁻)) → (α : Ω) → ♯ P α
into-Prop P f-zero f-succ f-lim zero = lift f-zero
into-Prop P f-zero f-succ f-lim (succ α) = liftf (f-succ α) (into-Prop P f-zero f-succ f-lim α)
into-Prop P f-zero f-succ f-lim (lim α⁻) = liftf (f-lim α⁻) (lift λ n → proof (into-Prop P f-zero f-succ f-lim (α⁻ n)))
into-Prop P f-zero f-succ f-lim (equiv {α} {β} p q i) =
  prop-is-dprop (λ i → ♯-prop {P (equiv {α} {β} p q i)}) (into-Prop P f-zero f-succ f-lim α) (into-Prop P f-zero f-succ f-lim β) i
into-Prop P f-zero f-succ f-lim (Ω-set α β p q i j) = lift {!!}

zero ≤ β = ⊤
succ α ≤ β = α < β
lim α⁻ ≤ β = ∀ n → α⁻ n ≤ β
equiv {α₁} {α₂} u v i ≤ β = bisim-path bisim i
  where
    bisim : α₁ ≤ β ⇔ α₂ ≤ β
    ltr bisim p = ≤-≤ α₂ α₁ β (proof v) p
    rtl bisim p = ≤-≤ α₁ α₂ β (proof u) p
Ω-set α₁ α₂ p q i₁ i₂ ≤ β = {!!}

α < β = {!!}

≤-≤ α = proof (into-Prop (λ α → ∀ β γ → α ≤ β → β ≤ γ → α ≤ γ) {!!} {!!} {!!} α) 
