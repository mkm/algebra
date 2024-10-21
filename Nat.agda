{-# OPTIONS --cubical --prop #-}
module Nat where

open import Prelude public
open import Path
open import Logic
open import Truncation
open import Decidable
open import String
open import Show

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

_+_ : ℕ → ℕ → ℕ
zero + n = n
succ m + n = succ (m + n)

infixr 50 _+_

_∖_ : ℕ → ℕ → ℕ
m ∖ zero = m
m ∖ succ n = pred (m ∖ n)

infix 50 _∖_

_·_ : ℕ → ℕ → ℕ
zero · _ = zero
succ m · n = m · n + n

infixr 60 _·_

+-zero-right : (a : ℕ) → a + zero ≡ a
+-zero-right zero _ = zero
+-zero-right (succ a) i = succ (+-zero-right a i)

+-succ-right : (a b : ℕ) → a + succ b ≡ succ (a + b)
+-succ-right zero b _ = succ b
+-succ-right (succ a) b i = succ (+-succ-right a b i)

+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c _ = b + c
+-assoc (succ a) b c i = succ (+-assoc a b c i)

+-comm : (a b : ℕ) → a + b ≡ b + a
+-comm zero b i = +-zero-right b (~ i)
+-comm (succ a) b = (λ i → succ (+-comm a b i)) ∘ (λ i → +-succ-right b a (~ i))

·-zero-right : (a : ℕ) → a · zero ≡ zero
·-zero-right zero _ = zero
·-zero-right (succ a) = +-zero-right (a · zero) ∘ ·-zero-right a

·-succ-right : (a b : ℕ) → a · (succ b) ≡ a · b + a
·-succ-right zero b _ = zero
·-succ-right (succ a) b =
  (λ i → ·-succ-right a b i + succ b) ∘
  (+-assoc (a · b) a (succ b)) ∘
  (λ i → a · b + +-succ-right a b i) ∘
  (λ i → a · b + +-comm (succ a) b i) ∘
  inv (+-assoc (a · b) b (succ a))

·-comm : (a b : ℕ) → a · b ≡ b · a
·-comm zero b i = ·-zero-right b (~ i)
·-comm (succ a) b = (λ i → ·-comm a b i + b) ∘ (λ i → ·-succ-right b a (~ i))

·-dist-right : (a b c : ℕ) → a · (b + c) ≡ a · b + a · c
·-dist-right zero b c _ = zero
·-dist-right (succ a) b c =
  (λ i → ·-dist-right a b c i + b + c) ∘
  (λ i → +-assoc (a · b + a · c) b c (~ i)) ∘
  (λ i → +-assoc (a · b) (a · c) b i + c) ∘
  (λ i → (a · b + (+-comm (a · c) b i)) + c) ∘
  (λ i → (+-assoc (a · b) b (a · c) (~ i)) + c) ∘
  +-assoc (a · b + b) (a · c) c

·-dist-left : (a b c : ℕ) → (a + b) · c ≡ a · c + b · c
·-dist-left a b c =
  ·-comm (a + b) c ∘
  ·-dist-right c a b ∘
  (λ i → ·-comm c a i + ·-comm c b i)

·-assoc : (a b c : ℕ) → (a · b) · c ≡ a · (b · c)
·-assoc zero b c _ = zero
·-assoc (succ a) b c = ·-dist-left (a · b) b c ∘ (λ i → ·-assoc a b c i + b · c)

sgn : ℕ → ℕ
sgn zero = 0
sgn (succ _) = 1

2^ : ℕ → ℕ
2^ zero = 1
2^ (succ n) = 2 · 2^ n

max : ℕ → ℕ → ℕ
max m n = m + (n ∖ m)

min : ℕ → ℕ → ℕ
min m n = n ∖ (n ∖ m)

is-zero : ℕ → Prop
is-zero zero = ⊤
is-zero (succ _) = ⊥

zero≢succ : ∀ {a} → zero ≢ succ a
zero≢succ p = proof (transp (λ t → ♯ (is-zero (p t))) i0 (lift top))

succ-inj : {a b : ℕ} → succ a ≡ succ b → a ≡ b
succ-inj {a} {b} p i = pred (p i)

dec-eq : (a b : ℕ) → Dec (a ≡ b)
dec-eq zero zero = yes id
dec-eq zero (succ b) = no zero≢succ
dec-eq (succ a) zero = no λ p → zero≢succ (inv p)
dec-eq (succ a) (succ b) with dec-eq a b
dec-eq (succ a) (succ b) | yes p = yes λ i → succ (p i)
dec-eq (succ a) (succ b) | no np = no λ p → np (succ-inj p)

ℕ-set : is-set ℕ
ℕ-set = dec-eq-set dec-eq

iterate-path : {A : Type} {x : A} → ℕ → x ≡ x → x ≡ x
iterate-path zero _ = id
iterate-path (succ n) p = iterate-path n p ∘ p

instance
  show-ℕ : Show ℕ
  Show.show show-ℕ = f
    where
      f : ℕ → String
      f zero = "z"
      f (succ n) = "s" ⋯ f n
