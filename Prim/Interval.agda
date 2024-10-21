{-# OPTIONS --cubical #-}
module Prim.Interval where

open import Prim.Core

open import Agda.Primitive.Cubical
  using (IUniv; I; i0; i1; IsOne; Partial; PartialP)
  renaming (primIMin to _∧_; primIMax to _∨_; primINeg to ~_; itIsOne to is-one; isOneEmpty to is-one-empty; primTransp to transp; primHComp to hcomp′; primComp to comp′)
  public

open import Agda.Builtin.Cubical.Path
  renaming (PathP to Path)
  public

open import Agda.Builtin.Cubical.Sub
  using (Sub)
  renaming (inS to sub; primSubOut to unsub)
  public

import Agda.Builtin.Cubical.HCompU

_≈_ : I → I → I
i ≈ j = (i ∧ j) ∨ (~ i ∧ ~ j)

infix 40 _≈_

∂ : I → I
∂ i = i ∨ ~ i

hcomp : ∀ {ℓ} {A : Type ℓ} (φ : I)
  → ((t : I) → Partial (φ ∨ t ≈ i0) A) → A
hcomp φ cube = hcomp′ (λ { t (φ = i1) → cube t is-one }) (cube i0 is-one)

comp : {ℓ : I → Level} (A : (i : I) → Type (ℓ i)) (φ : I)
  → ((t : I) → Partial (φ ∨ t ≈ i0) (A t)) → A i1
comp A φ cube = comp′ A (λ { t (φ = i1) → cube t is-one }) (cube i0 is-one)

wsub : ∀ {ℓ} {A : Type ℓ} (φ : I) (x : Partial φ A) (y : A) → PartialP φ (λ o → y ≡ x o) → Sub A φ x
wsub φ x y p = sub (hcomp φ (λ { i (φ = i1) → p is-one i ; i (i = i0) → y })) 
