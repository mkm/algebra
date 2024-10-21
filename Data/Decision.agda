{-# OPTIONS --cubical --erasure #-}
module Data.Decision where

open import Prelude
open import Data.Truncation.Base
open import Data.Truncation

data Dec {ℓ} (A : Type ℓ) : Type ℓ where
  yes : A → Dec A
  no : ¬ A → Dec A

dec-prop : ∀ {ℓ} {A : Type ℓ} → IsProp A → IsProp (Dec A)
dec-prop A-prop (yes α) (yes β) i = yes $ A-prop α β i
dec-prop A-prop (yes α) (no β) = absurd $ β α
dec-prop A-prop (no α) (yes β) = absurd $ α β
dec-prop A-prop (no α) (no β) i = no λ γ → ⊥-prop (α γ) (β γ) i

choose : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → Dec A → B → B → B
choose (yes _) x _ = x
choose (no _) _ y = y

is-yes : ∀ {ℓ} {A : Type ℓ} → Dec A → Bool
is-yes (yes _) = true
is-yes (no _) = false
