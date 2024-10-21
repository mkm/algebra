{-# OPTIONS --cubical --safe #-}
module Bad where

open import Cubical.Core.Everything

data ⊥ : Type where

data T : Type where
  c : T
  pair : T → T → T
  c-unit : ∀ x → pair c x ≡ x

data IsPair : T → Type where
  is-pair : ∀ x y → IsPair (pair x y)

all-pairs : ∀ x → IsPair x
all-pairs x = transp (λ i → IsPair (c-unit x i)) i0 (is-pair c x)

f : T → ⊥
g : (x : T) → IsPair x → ⊥

f x = g x (all-pairs x)
g .(pair x y) (is-pair x y) = f x

nope : ⊥
nope = f c
