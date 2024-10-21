{-# OPTIONS --cubical --erasure #-}
module Path.Equiv.Univalence where

open import Prelude
open import Path.Comp
open import Path.Equiv
open import Data.Truncation.Base

path-equiv-equiv : ∀ {ℓ} {A B : Type ℓ} → IsEquiv (path-equiv {A = A} {B = B})
linv path-equiv-equiv = equiv-path
rinv path-equiv-equiv = equiv-path
is-linv (path-equiv-equiv {A = A} {B = B}) i p j = Glue B T α
  where
    T : Partial (∂ i ∨ ∂ j) (Type _)
    T (i = i0) = equiv-path (path-equiv p) j
    T (i = i1) = p j
    T (j = i0) = A
    T (j = i1) = B
    α : PartialP (∂ i ∨ ∂ j) λ o → T o ≅ B
    α (i = i0) = β
      where
        f : (j : I) → equiv-path (path-equiv p) j → B
        f j = unglue {e = λ { (j = i0) → path-equiv p ; (j = i1) → ≅-id }}
        β : equiv-path (path-equiv p) j ≅ B
        fun β = f j
        is-equiv β = dprop (λ j → IsEquiv (f j)) equiv-prop (transport-equiv p) (id-equiv _) j
    α (i = i1) = β
      where
        β : p j ≅ B
        fun β = transp (λ t → p (j ∨ t)) (j ≈ i1)
        is-equiv β = dprop (λ j → IsEquiv (transp (λ t → p (j ∨ t)) (j ≈ i1))) equiv-prop (transport-equiv p) (id-equiv _) j
    α (j = i0) = path-equiv p
    α (j = i1) = ≅-id
is-rinv (path-equiv-equiv {A = A} {B = B}) i α = β
  where
    f : (i : I) → A → B
    f i a = hcomp-empty (transpot-id i (transpot-id i (fun α a))) i
    β : A ≅ B
    fun β = f i
    is-equiv β = dprop (λ i → IsEquiv (f i)) equiv-prop (transport-equiv (equiv-path α)) (is-equiv α) i

univ : ∀ {ℓ} {A B : Type ℓ} → (A ≡ B) ≅ (A ≅ B)
fun univ = path-equiv
is-equiv univ = path-equiv-equiv

refl-path-equiv : ∀ {ℓ} (A : Type ℓ) → equiv-path ≅-id ≡ refl-at A
refl-path-equiv A i =
  hcomp (∂ i) λ where
    j (i = i0) → is-linv path-equiv-equiv j (equiv-path ≅-id)
    j (j = i0) → equiv-path (lemma i)
    j (i = i1) → is-linv path-equiv-equiv j (refl-at A)
  where
    lemma : path-equiv (equiv-path ≅-id) ≡ path-equiv (refl-at A)
    lemma = equiv-equal _ _ λ i x → shadow-id i (transpot-id i (transpot x))

transport-inj₁ : ∀ {ℓ} {A B : Type ℓ} (p q : A ≡ B) → transport p ≡ transport q → p ≡ q
transport-inj₁ p q r i =
  hcomp (∂ i) λ where
    j (i = i0) → is-linv path-equiv-equiv j p
    j (j = i0) → equiv-path (α i)
    j (i = i1) → is-linv path-equiv-equiv j q
  where
    α : path-equiv p ≡ path-equiv q
    fun (α i) = r i
    is-equiv (α i) = dprop (λ i → IsEquiv (r i)) equiv-prop (transport-equiv p) (transport-equiv q) i

transport-inj₂ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x y : A) → transport p x ≡ transport p y → x ≡ y
transport-inj₂ p x y q i =
  hcomp (∂ i) λ where
    j (i = i0) → is-linv (transport-equiv p) j x
    j (j = i0) → transport (inv p) (q i)
    j (i = i1) → is-linv (transport-equiv p) j y
