{-# OPTIONS --cubical --erasure #-}
module Data.Function where

open import Prelude
open import Path.Equiv

Π : ∀ {ℓ ℓ′} {A : Type ℓ} (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
Π B = ∀ x → B x

pi-path : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} {f g : Π B} → (∀ x → f x ≡ g x) → f ≡ g
pi-path p i x = p x i

pi-path-equiv : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} (f g : Π B) → (f ≡ g) ≅ (∀ x → f x ≡ g x)
fun (pi-path-equiv f g) p x i = p i x
linv (is-equiv (pi-path-equiv f g)) p i x = p x i
rinv (is-equiv (pi-path-equiv f g)) p i x = p x i
is-linv (is-equiv (pi-path-equiv f g)) i p j x = p j x
is-rinv (is-equiv (pi-path-equiv f g)) i p j x = p j x

pi-path-char : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} (f g : Π B) → (f ≡ g) ≡ (∀ x → f x ≡ g x)
pi-path-char f g = equiv-path (pi-path-equiv f g)
