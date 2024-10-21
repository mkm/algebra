{-# OPTIONS --cubical --erasure #-}
module Data.OrdMap where

open import Prelude
open import Relation.PartialOrder

data OrdMap {ℓ ℓ′ ℓ″} {A : Type ℓ} (_≤_ : A → A → Type ℓ′) (B : Type ℓ″) : Type (ℓ ⊔ ℓ′ ⊔ ℓ″) where
  leaf : OrdMap _≤_ B
