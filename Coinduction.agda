{-# OPTIONS --cubical --prop --guardedness #-}
module Coinduction where

open import Path

record _° {ℓ} (A : Type ℓ) : Type ℓ where
  coinductive
  constructor delay
  field
    force : A

open _° public

infixl 1 _°
