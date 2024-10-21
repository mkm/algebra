{-# OPTIONS --cubical --erasure #-}
module Algebra.Monoid where

open import Prelude

private
  variable
    ℓ : Level

record IsMonoid (A : Type ℓ) : Type ℓ where
  field
    ε : A
    _·_ : A → A → A
    ε-left : ∀ x → ε · x ≡ x
    ε-right : ∀ x → x · ε ≡ x
    ·-assoc : ∀ x y z → (x · y) · z ≡ x · (y · z)
