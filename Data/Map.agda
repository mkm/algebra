{-# OPTIONS --cubical #-}
module Data.Map where

open import Prelude
open import Algebra.Monoid

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

record IsMap (K : Type ℓ₁) : Typeω where
  field
    Map : {A : K → Type ℓ} (M : (k : K) → IsMonoid (A k)) → Type ℓ
    empty : {A : K → Type ℓ} {M : (k : K) → IsMonoid (A k)} → Map M
    singleton : {A : K → Type ℓ} {M : (k : K) → IsMonoid (A k)} → (k : K) → A k → Map M
    union : {A : K → Type ℓ} {M : (k : K) → IsMonoid (A k)} → Map M → Map M → Map M
    {-
    intersection : {A : K → Type ℓ₂} {B : K → Type ℓ₃} {C : K → Type ℓ₄} → ({k : K} → A k → B k → C k) → Map A → Map B → Map C
    lookup : {A : K → Type ℓ} → (k : K) → Map A → A k
    -}

⊤-map : IsMap ⊤
IsMap.Map ⊤-map {A = A} M = A tt
IsMap.empty ⊤-map {M = M} = ε
  where open IsMonoid (M tt)
IsMap.singleton ⊤-map tt = id
IsMap.union ⊤-map {M = M} = _·_
  where open IsMonoid (M tt)
