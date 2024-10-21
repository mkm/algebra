{-# OPTIONS --cubical --erasure --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Algebra.AbGroup.Free where

open import Prelude
open import Path.Comp
open import Data.Bool
open import Data.Int renaming (_+_ to _+′_) hiding (+-assoc; +-comm)
open import Data.Fin
open import Data.Sigma
open import Data.Decision
open import Data.Function
open import Data.Truncation.Base

private
  variable
    ℓ : Level
    A : Type ℓ

data Free {ℓ} (A : Type ℓ) : Type ℓ

data _∼_ {A : Type ℓ} : Free A → Free A → Type ℓ

infix 10 _∼_

data Free A where
  ⟨_⟩ : A → Free A
  ε : Free A
  _+_ : Free A → Free A → Free A
  -_ : Free A → Free A
  sim : ∀ {x y} → x ∼ y → x ≡ y
  free-set : IsSet (Free A)

infixr 40 _+_
infixr 50 -_

data _∼_ where
  ε-left : ∀ x → ε + x ∼ x
  neg-left : ∀ x → (- x) + x ∼ ε
  +-assoc : ∀ x y z → (x + y) + z ∼ x + (y + z)
  +-comm : ∀ x y → x + y ∼ y + x

record FinMap {ℓ} (A : Type ℓ) : Type ℓ where
  field
    occurence : A → ℤ
    support : Finite (Σ A λ a → So $ is-nonzero (occurence a))

open FinMap public

module _ (_≟_ : (x y : A) → Dec (x ≡ y)) where

  to-fin-map : Free A → FinMap A
  to-fin-map ⟨ a ⟩ = λ where
    .occurence → λ b → choose (a ≟ b) (pos 1) (pos 0)
    .support → 1 , forget₀ e
      where
        a-witness : So $ is-nonzero (choose (a ≟ a) (pos 1) (pos 0))
        a-witness with a ≟ a
        a-witness | yes _ = oh
        a-witness | no p = absurd $ p refl
        e : Σ A (λ b → So $ is-nonzero (choose (a ≟ b) (pos 1) (pos 0))) ≅ Fin 1
        fun e _ = fzero
        linv (is-equiv e) _ = a , a-witness
        rinv (is-equiv e) _ = a , a-witness
        is-linv (is-equiv e) = pi-path λ (b , b-witness) → Σ-path (the (a ≡ b) {! !}) {! !} -- i (b , b-witness) = {! !}
        is-rinv (is-equiv e) = {! !}
  to-fin-map ε = λ where
    .occurence → λ _ → pos 0
    .support → 0 , forget₀ e
      where
        e : Σ A (λ _ → So false) ≅ Fin 0
        fun e (_ , ())
        linv (is-equiv e) ()
        rinv (is-equiv e) ()
        is-linv (is-equiv e) _ (_ , ())
        is-rinv (is-equiv e) _ ()
  to-fin-map (x + y) = {! !}
  to-fin-map (- x) = λ where
    .occurence → λ a → negate $ occurence (to-fin-map x) a
    .support → {! !}
  to-fin-map (sim s i) = {! !}
  to-fin-map (free-set x y p q i j) = {! !}
