{-# OPTIONS --cubical --prop #-}
module Sum where

open import Path
open import Logic

data _⊕_ (A B : Set) : Set where
  lft : A → A ⊕ B
  rgt : B → A ⊕ B
