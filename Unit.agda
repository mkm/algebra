{-# OPTIONS --cubical --prop #-}
module Unit where

open import Path
open import String
open import Show

record Unit : Type where
  constructor unit

instance
  show-Unit : Show Unit
  Show.show show-Unit _ = "unit"
