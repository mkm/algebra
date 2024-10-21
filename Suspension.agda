{-# OPTIONS --cubical --prop #-}
module Suspension where

open import Agda.Primitive
open import Path
open import Logic
open import Nat

data Susp (A : Type) : Type where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south

S : ℕ → Type
S zero = Bool
S (succ n) = Susp (S n)

base : ∀ {n} → S n
base {zero} = true
base {succ _} = north

record L (n : ℕ) {A : Type} (a : A) : Type where
  field
    path : S n → A
    boundary : path base ≡ a

open L public

{-
Cube : ℕ → Type → Type
Cube zero A = A
Cube (succ n) A = {!!}
-}
