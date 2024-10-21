{-# OPTIONS --cubical --prop #-}
module Tensor where

open import Path

data _⊗_ (A B : Type) : Type where
  _,_ : A → B → A ⊗ B
  _∣_ : {a a′ : A} {b b′ : B} → a ≡ a′ → b ≡ b′ → a , b ≡ a′ , b′
  ∣-id-left : {a : A} {b : B} (q : b ≡ b) → (_ ⊢ a) ∣ q ≡ (_ ⊢ a , b)
  ∣-id-right : {a : A} {b : B} (p : a ≡ a) → p ∣ (_ ⊢ b) ≡ (_ ⊢ a , b)
  ∣-∘-left : {a : A} {b : B} (p₁ p₂ : a ≡ a) (q : b ≡ b) → (p₁ ∘ p₂) ∣ q ≡ (p₁ ∣ q) ∘ (p₂ ∣ q)
  ⊗-groupoid : is-groupoid (A ⊗ B)

infixr 10 _,_ _∣_
