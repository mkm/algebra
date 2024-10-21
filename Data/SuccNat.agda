{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.SuccNat where

open import Prelude
import Data.Nat as N
open import Data.Nat renaming (_+_ to _+′_; _·_ to _·′_)

record ℕ₊ : Type where
  constructor succ₊
  field
    pred₊ : ℕ

open ℕ₊ public

as-succ : ℕ₊ → ℕ
as-succ = succ ∘ pred₊

_+_ : ℕ₊ → ℕ₊ → ℕ₊
pred₊ (m + n) = succ (pred₊ m +′ pred₊ n)

_·_ : ℕ₊ → ℕ₊ → ℕ₊
pred₊ (m · n) = as-succ m +′ as-succ n +′ pred₊ m ·′ pred₊ n
