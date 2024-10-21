{-# OPTIONS --cubical --erasure #-}
module Path.Strict where

open import Prelude
open import Path.Comp

record ◆ {ℓ} (A : Type ℓ) : SSet ℓ where
  constructor ↑
  field
    ↓ : A

open ◆ public

data _＝_ {ℓ} {A : SSet ℓ} (x : A) : A → SSet ℓ where
  instance unify : x ＝ x

{-# BUILTIN EQUALITY _＝_ #-}

unify-path : ∀ {ℓ} {A : Type ℓ} {x y : A} → ↑ x ＝ ↑ y → x ≡ y
unify-path unify = refl

uip : ∀ {ℓ} {A : SSet ℓ} {x y : A} (p q : x ＝ y) → p ＝ q
uip unify unify = unify

apₛ : ∀ {ℓ₁ ℓ₂} {A : SSet ℓ₁} {B : SSet ℓ₂} (f : A → B) {x y : A} → x ＝ y → f x ＝ f y
apₛ f unify = unify

transportₛ : ∀ {ℓ₁ ℓ₂} {A : SSet ℓ₁} (B : A → SSet ℓ₂) {x y : A} → x ＝ y → B x → B y
transportₛ B unify x = x
