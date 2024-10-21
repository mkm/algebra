{-# OPTIONS --cubical --prop #-}
module UnordPair where

open import Path

data _² (A : Type) : Type where
  _,_ : A → A → A ²
  swap : (x y : A) → x , y ≡ y , x

from² : {A B : Type} → (f : A → A → B) → (∀ x y → f x y ≡ f y x) → A ² → B
from² f s (x , y) = f x y
from² f s (swap x y i) = s x y i
