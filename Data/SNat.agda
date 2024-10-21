{-# OPTIONS --cubical --erasure #-}
module Data.SNat where

open import Prelude

data ℕₛ : SSet where
  zeroₛ : ℕₛ
  succₛ : ℕₛ → ℕₛ

weak-nat : ℕₛ → ℕ
weak-nat zeroₛ = zero
weak-nat (succₛ n) = succ (weak-nat n)
