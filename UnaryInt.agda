{-# OPTIONS --cubical --prop #-}
module UnaryInt where

open import Path
open import Logic
open import Nat using (ℕ)
import Nat as N
open import Decidable

data ℤ : Type where
  zero : ℤ
  succ : ℤ → ℤ
  pred : ℤ → ℤ
  succ-pred : (n : ℤ) → succ (pred n) ≡ pred (succ n)

pos : ℕ → ℤ
pos ℕ.zero = zero
pos (ℕ.succ n) = succ (pos n)

neg : ℕ → ℤ
neg ℕ.zero = zero
neg (ℕ.succ n) = succ (neg n)

dec-eq-pos : (m : ℤ) (n : ℕ) → Dec (m ≡ pos n)
dec-eq-neg : (m : ℤ) (n : ℕ) → Dec (m ≡ neg n)

dec-eq-pos zero ℕ.zero = yes id
dec-eq-pos zero (ℕ.succ n) = no {!!}
dec-eq-pos (succ m) ℕ.zero with dec-eq-neg m 1
dec-eq-pos (succ m) ℕ.zero | d = {!!}
dec-eq-pos (succ m) (ℕ.succ n) with dec-eq-pos m n
dec-eq-pos (succ m) (ℕ.succ n) | yes p = yes λ i → succ (p i)
dec-eq-pos (succ m) (ℕ.succ n) | no contra = no {!!}
dec-eq-pos (pred m) ℕ.zero with dec-eq-pos m 1
dec-eq-pos (pred m) ℕ.zero | d = {!!}
dec-eq-pos (pred m) (ℕ.succ n) = {!!}
dec-eq-pos (succ-pred m i) n = {!!}
dec-eq-neg m n = {!!}

dec-eq : (m n : ℤ) → Dec (m ≡ n)
dec-eq zero n = {!!}
dec-eq (succ m) n = {!!}
dec-eq (pred m) n = {!!}
dec-eq (succ-pred m i) n = {!!}

_+_ : ℤ → ℤ → ℤ
zero + n = n
succ m + n = succ (m + n)
pred m + n = pred (m + n)
succ-pred m i + n = succ-pred (m + n) i

infixr 50 _+_

-_ : ℤ → ℤ
- zero = zero
- succ n = pred (- n)
- pred n = succ (- n)
- succ-pred n i = succ-pred (- n) (~ i)

infix 51 -_

_─_ : ℤ → ℤ → ℤ
m ─ n = m + - n

infix 50 _─_

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero b c _ = b + c
+-assoc (succ a) b c i = succ (+-assoc a b c i)
+-assoc (pred a) b c i = pred (+-assoc a b c i)
+-assoc (succ-pred a i) b c = {!!}

_·_ : ℤ → ℤ → ℤ
zero · _ = zero
succ m · n = m · n + n
pred m · n = m · n ─ n
succ-pred m i · n = {!!}

infixr 60 _·_
