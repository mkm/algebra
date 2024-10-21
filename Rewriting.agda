{-# OPTIONS --rewriting --confluence-check #-}
module Rewriting where

data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set where
  refl : x ≡ x

infix 1 _≡_

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}

refl-at : ∀ {ℓ} {A : Set ℓ} (x : A) → x ≡ x
refl-at _ = refl

cong : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong _ refl = refl

cong₂ : ∀ {ℓ} {A B C : Set ℓ} (f : A → B → C) {x₁ y₁ x₂ y₂} → x₁ ≡ y₁ → x₂ ≡ y₂ → f x₁ x₂ ≡ f y₁ y₂
cong₂ _ refl refl = refl

_∘_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∘ p = p

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

succ-inj : ∀ {m n} → succ m ≡ succ n → m ≡ n
succ-inj refl = refl

_+_ : ℕ → ℕ → ℕ
zero + n = n
succ m + n = succ (m + n)

infix 20 _+_

+-zeroᵣ : ∀ n → n + 0 ≡ n
+-zeroᵣ zero = refl
+-zeroᵣ (succ n) = cong succ (+-zeroᵣ n)

+-succ-zero : ∀ n → succ n + 0 ≡ succ n
+-succ-zero n = cong succ (+-zeroᵣ n)

{-# REWRITE +-zeroᵣ +-succ-zero #-}

+-succᵣ : ∀ m n → m + succ n ≡ succ (m + n)
+-succᵣ zero n = refl
+-succᵣ (succ m) n = cong succ (+-succᵣ m n)

+-zero-succ : ∀ n → 0 + succ n ≡ succ n
+-zero-succ n = refl

+-succ-succ : ∀ m n → succ m + succ n ≡ succ (succ (m + n))
+-succ-succ m n = cong succ (+-succᵣ m n)

{-# REWRITE +-succᵣ +-zero-succ +-succ-succ #-}

+-assoc : ∀ m n p → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (succ m) n p = cong succ (+-assoc m n p)

pred : ℕ → ℕ
pred zero = 0
pred (succ m) = m

_∖_ : ℕ → ℕ → ℕ
m ∖ zero = m
m ∖ succ n = pred (m ∖ n)

infix 20 _∖_

∖-succ : ∀ m n → succ m ∖ succ n ≡ m ∖ n
∖-succ m zero = refl
∖-succ m (succ n) = cong pred (∖-succ m n)

∖-contract : ∀ m n p → ((m + n) ∖ p) ∖ m ≡ n ∖ p
∖-contract zero n p = refl
∖-contract (succ m) n zero = ∖-succ (m + n) m ∘ ∖-contract m n 0
∖-contract (succ m) n (succ p) = cong pred (cong₂ _∖_ (∖-succ (m + n) p) (refl-at m) ∘ ∖-contract m n p) 

∖-contract-zero : ∀ n p → ((0 + n) ∖ p) ∖ 0 ≡ n ∖ p
∖-contract-zero n p = refl

∖-contract-succ : ∀ m n p → ((succ m + n) ∖ p) ∖ succ m ≡ n ∖ p
∖-contract-succ m n p = ∖-contract (succ m) n p

{-# REWRITE ∖-contract ∖-contract-zero ∖-contract-succ #-}

∖-same : ∀ m → m ∖ m ≡ 0
∖-same zero = refl
∖-same (succ m) = ∖-succ m m ∘ ∖-same m

-- {-# REWRITE ∖-succ #-}
