{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Delay where

open import Prelude

record Delay {ℓ} (A : Type ℓ) : Type ℓ where
  coinductive
  constructor delay
  field
    force : A

open Delay public
