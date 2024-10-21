{-# OPTIONS --cubical #-}
module Data.Quotient where

open import Prelude
open import Path.Comp
open import Data.Suspension

infixl 10 _/_
data _/_ {ℓ ℓ′} (A : Type ℓ) (R : A → A → Type ℓ′) : Type (ℓ ⊔ ℓ′)

data is-[] {ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′} : A / R → Type (ℓ ⊔ ℓ′)

data _/_ A R where
  [_] : A → A / R
  rel : ∀ x y → R x y → [ x ] ≡ [ y ]
  squash : ∀ n (p : Sⁿ n → A / R) → ¬ (∀ x₀ → is-[] (p x₀)) → (x : Sⁿ n) → p ≡ const (p north)
  -- squash : ∀ {n} (f : Sⁿ n → A / R) → ¬ (Σ (Sⁿ n → A) λ f₀ → f ≡ [_] ∘ f₀) → (x : Sⁿ n) → f ≡ const (f north)

data is-[] where
  indeed : ∀ x → is-[] [ x ]

data Rel : Bool → Bool → Type where
  ff : Rel false false

ff-path : Pathₖ (Bool / Rel) [ false ] [ false ]
ff-path = rel false false ff

triv : ff-path ≡ refl
triv = {!squash 1 p!}
  where
    p : Sⁿ 1 → Bool / Rel
    p north = [ false ]
    p south = [ false ]
    p (merid _ i) = ff-path i
    e : ¬ ((x₀ : Sⁿ 1) → is-[] (p x₀))
    e α = {!!}
