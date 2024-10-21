{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Nat where

open import Prelude
open import Path.Comp
open import Path.Equiv
open import Data.Bool
open import Data.Truncation

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

is-zero : ℕ → Bool
is-zero zero = true
is-zero (succ _) = false

is-succ : ℕ → Bool
is-succ zero = false
is-succ (succ _) = true

zero-vs-succ : ∀ {n} → zero ≢ succ n
zero-vs-succ p = false-vs-true λ i → is-succ (p i)

succ-inj : ∀ {m n} → succ m ≡ succ n → m ≡ n
succ-inj p i = pred (p i)

succ-ap-inj : ∀ {m n} (p : succ m ≡ succ n) → ap succ (succ-inj p) ≡ p
succ-ap-inj {m = m} p i j = lemma (p j) (λ i → p (i ∧ j)) i
  where
    lemma : (pⱼ : ℕ) → succ m ≡ pⱼ → succ (pred pⱼ) ≡ pⱼ
    lemma zero α = absurd $ zero-vs-succ (inv α)
    lemma (succ pⱼ) α = refl

nat-vs-succ : ∀ {n} → n ≢ succ n
nat-vs-succ {zero} = zero-vs-succ
nat-vs-succ {succ n} p = nat-vs-succ (succ-inj p)

infix 25 _≟_
_≟_ : ℕ → ℕ → Bool
zero ≟ zero = true
zero ≟ succ _ = false
succ _ ≟ zero = false
succ m ≟ succ n = m ≟ n

≟-sound : ∀ m n → So (m ≟ n) → m ≡ n
≟-sound zero zero _ = refl
≟-sound (succ m) (succ n) = ap succ ∘ ≟-sound m n

≟-refl : ∀ n → So (n ≟ n)
≟-refl zero = oh
≟-refl (succ n) = ≟-refl n

≟-complete : ∀ m n → m ≡ n → So (m ≟ n)
≟-complete zero zero p = oh
≟-complete zero (succ n) p = absurd $ zero-vs-succ p
≟-complete (succ m) zero p = absurd $ zero-vs-succ (inv p)
≟-complete (succ m) (succ n) p = ≟-complete m n (succ-inj p)

≟-sound-refl : ∀ n → ≟-sound n n (≟-refl n) ≡ refl
≟-sound-refl zero = refl
≟-sound-refl (succ n) i = ap succ (≟-sound-refl n i)

ℕ-set : IsSet ℕ
ℕ-set zero zero p q i j = lemma (p j) (q j) (λ i → p (i ∧ j)) (λ i → q (i ∧ j)) i
  where
    lemma : ∀ pⱼ qⱼ → zero ≡ pⱼ → zero ≡ qⱼ → pⱼ ≡ qⱼ
    lemma zero zero p′ q′ = refl
    lemma zero (succ _) p′ q′ = q′
    lemma (succ _) _ p′ q′ = inv p′ ■ q′ 
ℕ-set zero (succ _) p q = absurd $ zero-vs-succ p
ℕ-set (succ m) zero p q = absurd $ zero-vs-succ (inv p)
ℕ-set (succ m) (succ n) p q i =
  hcomp (∂ i) λ where
    j (i = i0) → succ-ap-inj p j
    j (j = i0) → ap succ (ℕ-set m n (succ-inj p) (succ-inj q) i)
    j (i = i1) → succ-ap-inj q j

can-path : {m n : ℕ} → m ≡ n → m ≡ n
can-path {m = zero} {n = zero} p = refl
can-path {m = zero} {n = succ n} p = absurd $ zero-vs-succ p
can-path {m = succ m} {n = zero} p = absurd $ zero-vs-succ (inv p)
can-path {m = succ m} {n = succ n} p i = succ (can-path (succ-inj p) i)

infixr 50 _+_
_+_ : ℕ → ℕ → ℕ
zero + n = n
succ m + n = succ (m + n)

infixr 50 _+ᵣ_
_+ᵣ_ : ℕ → ℕ → ℕ
zero +ᵣ n = n
succ m +ᵣ n = m +ᵣ (succ n)

infixr 60 _·_
_·_ : ℕ → ℕ → ℕ
zero · n = zero
succ m · n = m · n + n

infix 50 _∖_
_∖_ : ℕ → ℕ → ℕ
m ∖ zero = m
m ∖ succ n = pred (m ∖ n)

max : ℕ → ℕ → ℕ
max zero n = n
max (succ m) n = succ (max m (pred n))

+-zero : ∀ n → n + 0 ≡ n
+-zero zero = refl
+-zero (succ n) i = succ (+-zero n i)

+-succ : ∀ m n → m + succ n ≡ succ (m + n)
+-succ zero n = refl
+-succ (succ m) n = ap succ (+-succ m n)

·-zero : ∀ n → n · 0 ≡ 0
·-zero zero = refl
·-zero (succ n) i = +-zero (·-zero n i) i

_+₃_+₃_ : ∀ x y z → (x + y) + z ≡ x + (y + z)
zero +₃ y +₃ z = refl
succ x +₃ y +₃ z = ap succ (x +₃ y +₃ z)

+-comm : ∀ x y → x + y ≡ y + x
+-comm zero y = inv (+-zero y)
+-comm (succ x) y = ap succ (+-comm x y) ■ inv (+-succ y x)

·-succ : ∀ m n → m · succ n ≡ m · n + m
·-succ zero n = refl
·-succ (succ m) n =
  (λ i → ·-succ m n i + succ n) ■
  ((m · n) +₃ m +₃ succ n) ■
  (λ i → m · n + +-comm m (succ n) i) ■
  (λ i → m · n + +-succ n m (~ i)) ■
  inv ((m · n) +₃ n +₃ succ m)

opaque
  ·-comm : ∀ x y → x · y ≡ y · x
  ·-comm zero y = inv (·-zero y)
  ·-comm (succ x) y = (λ i → ·-comm x y i + y) ■ inv (·-succ y x) 

infixr 50 _+-+ᵣ_
_+-+ᵣ_ : ∀ x y → x + y ≡ x +ᵣ y
zero +-+ᵣ y = refl
succ x +-+ᵣ y = inv (+-succ x y) ■ (x +-+ᵣ succ y)

+ᵣ-assoc : ∀ x y z → (x +ᵣ y) +ᵣ z ≡ y +ᵣ (x + z)
+ᵣ-assoc x y z = transport (λ i → ((x +-+ᵣ y) i +-+ᵣ z) i ≡ (y +-+ᵣ (x + z)) i) ((λ i → +-comm x y i + z) ■ (y +₃ x +₃ z))

+ᵣ-zero : ∀ n → n +ᵣ 0 ≡ n
+ᵣ-zero n = transport (λ i → (n +-+ᵣ 0) i ≡ n) (+-zero n)

∖-zero : ∀ n → 0 ∖ n ≡ 0
∖-zero zero = refl
∖-zero (succ n) i = pred (∖-zero n i)

∖-succ : ∀ m n → succ m ∖ succ n ≡ m ∖ n
∖-succ m zero = refl
∖-succ m (succ n) i = pred $ ∖-succ m n i
