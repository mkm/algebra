{-# OPTIONS --cubical --prop #-}
module Decidable where

open import Path
open import Truncation
open import Logic

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : ¬ A → Dec A

dec-inj : {A B : Set} (f : A → B) → (∀ {x y} → f x ≡ f y → x ≡ y) → {x y : A} → Dec (x ≡ y) → Dec (f x ≡ f y)
dec-inj f p (yes q) = yes λ i → f (q i)
dec-inj f p (no contra) = no λ q → contra (p q)

from-dec : {A : Set} → Dec A → ♭ A → A
from-dec (yes x) _ = x
from-dec (no contra) y = ⊥-elim (squash-contra y contra)

dec-path : {A : Set} → ((x y : A) → Dec (x ≡ y)) → (x y : A) → ♭ (x ≡ y) → x ≡ y
dec-path dec x y = from-dec (dec x y)

dec-square : {A : Set} → (dec : (x y : A) → Dec (x ≡ y)) → (x y : A) (p q : x ≡ y) → PathP (λ i → dec-path dec x x (squash id) i ≡ dec-path dec y y (squash id) i) p q
dec-square dec x y p q i j = dec-path dec (p j) (q j) (squash connection) i
  where
    connection : p j ≡ q j
    connection k = hcomp (λ h → λ { (k = i0) → p (h ∧ j)
                                  ; (k = i1) → q (h ∧ j) }) x

dec-eq-set : {A : Set} → ((x y : A) → Dec (x ≡ y)) → is-set A
dec-eq-set dec x y p q i j =
  hcomp (λ h → λ { (i = i0) → p j
                 ; (i = i1) → dec-square dec x y q q (~ h) j
                 ; (j = i0) → dec-path dec x x (squash id) (i ∧ ~ h)
                 ; (j = i1) → dec-path dec y y (squash id) (i ∧ ~ h) }) (dec-square dec x y p q i j)

{-
dec-eq-set {A} dec x y p q = {!!}
  where
    dec-id : (x : A) → x ≡ x
    dec-id x with dec x x
    dec-id x | yes r = r
    dec-id x | no nr = ⊥-elim (nr id)

    square : I → I → A
    square i j with dec (p i) (q i)
    square i j | yes r = r j
    square i j | no contra = ⊥-elim (contra λ k → hcomp (λ h → λ { (k = i0) → p (h ∧ i) ; (k = i1) → q (h ∧ i) }) x)
-}    
    
