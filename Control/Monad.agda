{-# OPTIONS --cubical --erasure #-}
module Control.Monad where

open import Prelude
open import Control.Functor

infixr 5 _>>_
record Monad (M : ∀ {ℓ} → Type ℓ → Type ℓ) : Typeω where
  field
    overlap ⦃ monad-functor ⦄ : Functor M
    pure : ∀ {ℓ} {A : Type ℓ} → A → M A
    _>>=_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → M A → (A → M B) → M B
    pure-bind : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (x : A) (f : A → M B) → pure x >>= f ≡ f x
    bind-pure : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (x : M A) (f : A → B) → x >>= pure ∘ f ≡ map f x
    bind-assoc : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (x : M A) (f : A → M B) (g : B → M C) → (x >>= f) >>= g ≡ x >>= (λ y → f y >>= g)

  infixr 5 _>>=_

open Monad ⦃ … ⦄ public

private
  variable
    M : ∀ {ℓ} → Type ℓ → Type ℓ

_>>_ : ∀ {ℓ₁ ℓ₂} ⦃ _ : Monad M ⦄ {A : Type ℓ₁} {B : Type ℓ₂} → M A → M B → M B
x >> y = x >>= const y

join : ∀ {ℓ} ⦃ _ : Monad M ⦄ {A : Type ℓ} → M (M A) → M A
join x = x >>= id

_<*>_ : ∀ {ℓ₁ ℓ₂} ⦃ _ : Monad M ⦄ {A : Type ℓ₁} {B : Type ℓ₂} → M (A → B) → M A → M B
f <*> x = do
  f′ ← f
  x′ ← x
  pure $ f′ x′
