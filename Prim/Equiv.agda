{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Prim.Equiv where

open import Prim.Core
open import Prim.Interval

record IsEquiv {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) : Type (ℓ₁ ⊔ ℓ₂) where
  field
    linv : B → A
    rinv : B → A
    is-linv : (λ (a : A) → linv (f a)) ≡ (λ a → a)
    is-rinv : (λ (b : B) → f (rinv b)) ≡ (λ b → b)

  is-linv′ : ∀ a → linv (f a) ≡ a
  is-linv′ a i = is-linv i a

  is-rinv′ : ∀ b → f (rinv b) ≡ b
  is-rinv′ b i = is-rinv i b

open IsEquiv public

infix 10 _≅_
record _≅_ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  field
    fun : A → B
    is-equiv : IsEquiv fun

open _≅_ public

equiv-proof : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) (α : A ≅ B) (b : B)
  → ∀ ψ (f : Partial ψ (Σ _ λ a → fun α a ≡ b)) → Sub (Σ _ λ a → fun α a ≡ b) ψ f
equiv-proof A B α b ψ f = sub (hcomp ψ (λ { i (ψ = i1) → lemma is-one i ; i (i = i0) → canonical }))
  where
    canonical : Σ _ λ a → fun α a ≡ b
    canonical = rinv (is-equiv α) b , λ i → is-rinv (is-equiv α) i b
    lrinv : linv (is-equiv α) ≡ rinv (is-equiv α)
    lrinv i x =
      hcomp (∂ i) λ where
        j (i = i0) → linv (is-equiv α) (is-rinv (is-equiv α) j x)
        j (j = i0) → linv (is-equiv α) (fun α (rinv (is-equiv α) x))
        j (i = i1) → is-linv (is-equiv α) j (rinv (is-equiv α) x)
    lemma : PartialP ψ (λ o → canonical ≡ f o)
    fst (lemma o i) =
      hcomp (∂ i) λ where
        j (i = i0) → lrinv j b
        j (j = i0) → linv (is-equiv α) (snd (f o) (~ i))
        j (i = i1) → is-linv (is-equiv α) j (fst (f o))
    snd (lemma o i) = {!!}

{-# BUILTIN EQUIV _≅_ #-}
{-# BUILTIN EQUIVFUN fun #-}
{-# BUILTIN EQUIVPROOF equiv-proof #-}
