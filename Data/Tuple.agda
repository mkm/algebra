{-# OPTIONS --cubical #-}
module Data.Tuple where

open import Prelude
open import Data.Vec

Tuple : ∀ {ℓ n} → Vec (Type ℓ) n → Type ℓ
Tuple [] = ⊤ as _
Tuple (A ∷ As) = A × Tuple As
