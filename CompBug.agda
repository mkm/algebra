{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical renaming (primComp to comp)

L : {A B : Set} {P : A ≡ B} {a : A} {b : B} (p : PathP (λ i → P i) a b) → Set
L p = p ≡ p

error : {P : I → Set} (p : (i : I) → P i) → L (λ i → p i)
error p i j = comp ? ? ?
