{-# OPTIONS --cubical --prop #-}
module LoopMonoid where

open import Path
open import List

data Base (A : Type) : Type where
  point : List A → Base A
  arrow : ∀ {xs} (x : A) → point xs ≡ point (x ∷ xs)

record Free (A : Type) : Type where
  field
    grade : List A
    elem : point [] ≡ point grade

open Free

⟨_⟩ : ∀ {A} → A → Free A
grade ⟨ a ⟩ = a ∷ []
elem ⟨ a ⟩ = arrow a

ε : ∀ {A} → Free A
grade ε = []
elem ε = id

_·_ : ∀ {A} → Free A → Free A → Free A
grade (x · y) = grade x ++ grade y
elem (x · y) = {!elem x !}
