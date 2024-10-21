{-# OPTIONS --cubical --guardedness #-}
module Data.CoNat where

open import Prelude
open import Path.Comp
open import Data.Bool
open import Topology.Compact

data ∞ℕ : Type

record ◆ℕ : Type

data ∞ℕ where
  ∞zero : ∞ℕ
  ∞succ : ◆ℕ → ∞ℕ

record ◆ℕ where
  coinductive
  field
    ◆pred : ∞ℕ

open ◆ℕ public

∞pred : ∞ℕ → ∞ℕ
∞pred ∞zero = ∞zero
∞pred (∞succ n) = ◆pred n

from-ℕ : ℕ → ∞ℕ
from-ℕ zero = ∞zero
from-ℕ (succ n) = ∞succ λ where
  .◆pred → from-ℕ n

∞ : ∞ℕ
∞ = ∞succ λ where
  .◆pred → ∞

is-∞succ : ∞ℕ → Bool
is-∞succ ∞zero = false
is-∞succ (∞succ _) = true

∞ℕ-witness : (f : ∞ℕ → Bool) → ∞ℕ
∞ℕ-witness f with f ∞zero
∞ℕ-witness f | false = ∞succ λ where
  .◆pred → ∞ℕ-witness (λ n → f $ ∞succ λ { .◆pred → n })
∞ℕ-witness f | true = ∞zero

∞ℕ-universal : (f : ∞ℕ → Bool) (x : ∞ℕ) → So (f x) → So (f (∞ℕ-witness f))
∞ℕ-universal f x α with inspect (f (∞ℕ-witness f)) | inspect (f x)
∞ℕ-universal f x α | false , p | false , p′ = absurd $ uh-oh (transport (λ i → So (p′ i)) α)
∞ℕ-universal f x α | false , p | true , p′ = {!!}
∞ℕ-universal f x α | true , p | b′ , p′ = transport (λ i → So (p (~ i))) oh

meh : ∞ℕ → Bool
meh = is-∞succ ∘ ∞pred ∘ ∞pred ∘ ∞pred

∞ℕ-compact : Compact ∞ℕ
witness ∞ℕ-compact = ∞ℕ-witness
universal ∞ℕ-compact = {!!}
