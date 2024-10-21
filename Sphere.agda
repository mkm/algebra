{-# OPTIONS --cubical --prop #-}
module Sphere where

open import Path

data S² : Type where
  base : S²
  surface : ⟪ base ⟫ =⟦ _ ⊢ base ≡ base ⟧= ⟪ base ⟫
