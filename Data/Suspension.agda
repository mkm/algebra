{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Suspension where

open import Prelude

data Susp {ℓ} (A : Type ℓ) : Type ℓ where
  north : Susp A
  south : Susp A
  merid : A → north ≡ south

Sn : ℕ → Type
Sn n = Susp $ iterate n Susp ⊥
