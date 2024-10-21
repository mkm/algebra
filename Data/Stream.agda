{-# OPTIONS --cubical --guardedness #-}
module Data.Stream where

open import Prelude

record Stream {ℓ} (A : Type ℓ) : Type ℓ where
  coinductive
  field
    head : A
    tail : Stream A

open Stream public

repeat : ∀ {ℓ} {A : Type ℓ} → A → Stream A
head (repeat x) = x
tail (repeat x) = repeat x
