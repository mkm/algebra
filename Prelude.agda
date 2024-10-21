{-# OPTIONS --cubical --erasure #-}
module Prelude where

open import Prim public

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level

id : {A : Type ℓ} → A → A
id x = x

infix 1 _$_
_$_ : {A : Type ℓ₁} {B : A → Type ℓ₂} (f : (a : A) → B a) (a : A) → B a
f $ x = f x

infixr 30 _∘_
_∘_ : {A : Type ℓ₁} {B : A → Type ℓ₂} {C : {a : A} → B a → Type ℓ₃}
  (f : {a : A} → (b : B a) → C b) (g : (a : A) → B a)
  → (a : A) → C (g a)
(f ∘ g) x = f (g x)

iterate : {A : Type ℓ} → ℕ → (A → A) → A → A
iterate zero _ = id
iterate (succ n) f = f ∘ iterate n f

const : {A : Type ℓ₁} {B : Type ℓ₂} → A → B → A
const x _ = x

flip : {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} → (A → B → C) → B → A → C
flip f x y = f y x

the : (A : Type ℓ) → A → A
the _ = id

theₛ : (A : SSet ℓ) → A → A
theₛ _ x = x

@0 erase : {A : Type ℓ} → A → A
erase = id

! : {A : Type ℓ} ⦃ _ : A ⦄ → A
! ⦃ x ⦄ = x

absurd : {A : Type ℓ} → ⊥ → A
absurd ()

absurdₑ : {A : Type ℓ} → @0 ⊥ → A
absurdₑ ()

infixr 10 ¬_
¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

infix 4 _≢_
_≢_ : {A : Type ℓ} → A → A → Type ℓ
x ≢ y = ¬ (x ≡ y)

inspect : ∀ {A : Type ℓ} → (x : A) → Σ A λ y → x ≡ y
fst (inspect x) = x
snd (inspect x) _ = x

record _as_ {ℓ′} (A : Type ℓ′) ℓ : Type (ℓ′ ⊔ ℓ) where
  eta-equality
  constructor promote
  field
    demote : A

open _as_ public

{-
open import Agda.Primitive using (lzero; lsuc; _⊔_) public
open import Cubical.Core.Everything

data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

level : ℕ → Level
level zero = lzero
level (succ n) = lsuc (level n)

record _as_ {ℓ′} (A : Type ℓ′) ℓ : Type (ℓ′ ⊔ ℓ) where
  eta-equality
  constructor promote
  field
    demote : A

open _as_ public

infixl 10 _as_
-}
