{-# OPTIONS --cubical #-}
module Data.Sphere where

open import Prelude
open import Path.Comp
open import Path.Equiv
open import Path.Equiv.Univalence
open import Data.Int
open import Data.Circle using (S¹; loop; loop-at; loop-loop-equiv; loop-loop-path) renaming (base to base′; winding-number to winding-number′)
open import Data.Show

data S² : Type where
  base : S²
  surf : Ω₂ base

meh : Pathₖ (S¹ ≅ S¹) ≅-id ≅-id
meh = equiv-equal ≅-id ≅-id λ i x → loop-at x i

surf-to-loop : S² → Type
surf-to-loop base = S¹
surf-to-loop (surf i j) = j ►
  hcomp (∂ i) λ where
    k (i = i0) → refl-path-equiv S¹ k
    k (k = i0) → equiv-path (α i)
    k (i = i1) → refl-path-equiv S¹ k
  where
    α : Pathₖ (S¹ ≅ S¹) ≅-id ≅-id
    α = equiv-equal ≅-id ≅-id λ i x → loop-at x i

winding-number : Ω₂ base → ℤ
winding-number p = winding-number′ γ  -- transport (λ i → surf-to-loop (p i i))
  where
    sq : Pathₖ (S¹ ≡ S¹) refl refl
    sq i j = surf-to-loop (p i j)
    α : Pathₖ (S¹ → S¹) id id
    α i = transport (sq i)
    β : Pathₖ (Σ S¹ Ω₁) (base′ , loop) (base′ , loop)
    β = transport (λ t → Pathₖ (loop-loop-path S¹ t) (transport-equiv-path (loop-loop-equiv S¹) id t) (transport-equiv-path (loop-loop-equiv S¹) id t)) α
    γ : Ω₁ base′
    γ i = fst (β i)
