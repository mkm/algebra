{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Show where

open import Prelude
open import Path.Comp
open import Data.String public

record Show {ℓ} (A : Type ℓ) : Type ℓ where
  coinductive
  field
    show : A → String
    instance next : {x : A} → Show (x ≡ x)

open Show ⦃ … ⦄ public

{-
record Coshow {ℓ} (A : Type ℓ) : Typeω where
  field
    coshow : ∀ {ℓ′} {B : A → Type ℓ′} ⦃ _ : ∀ {x} → Show (B x) ⦄ → ((x : A) → B x) → String

open Coshow ⦃ … ⦄ public
-}

map-show : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → (A → B) → Show B → Show A
show ⦃ map-show f ℬ ⦄ = show ⦃ ℬ ⦄ ∘ f
next ⦃ map-show f ℬ ⦄ = map-show (ap f) (next ⦃ ℬ ⦄)

{-
instance
  show-fun : ∀ {ℓ ℓ′ σ} {A : Type ℓ} {B : A → Type ℓ′} ⦃ 𝒜 : Coshow σ A ⦄ ⦃ ℬ : ∀ {σ′ x} → Show σ′ (B x) ⦄ → Show σ ((x : A) → B x)
  show ⦃ show-fun ⦄ f = coshow f
  next ⦃ show-fun {A = A} {B = B} ⦃ ℬ = ℬ ⦄ ⦄ {f} = map-show α (show-fun ⦃ ℬ = next ⦃ ℬ ⦄ ⦄) 
    where
      α : {f g : (x : A) → B x} (p : f ≡ g) (x : A) → f x ≡ g x
      α p x i = p i x
-}

show-refl : ∀ {ℓ} {A : Type ℓ} → Show A
show ⦃ show-refl ⦄ = const "refl"
next ⦃ show-refl ⦄ = show-refl

{-
instance
  type-path-show : ∀ {ℓ σ} {A B : Type ℓ} ⦃ _ : Coshow A ⦄ ⦃ _ : Show σ B ⦄ → Show σ (A ≡ B)
  show ⦃ type-path-show ⦃ 𝒜 ⦄ ⦃ ℬ ⦄ ⦄ = show ⦃ {!!} ⦄ ∘ transport
  next ⦃ type-path-show ⦄ = show-refl
-}
