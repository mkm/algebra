{-# OPTIONS --cubical --prop --type-in-type #-}
module Girard where

open import Path
open import Logic

data T : Type where
  c : ((A : Type) → A → A) → T

T-empty : T → ♯ ⊥
T-empty (c f) = T-empty (f T (c f))

absurd : ⊥
absurd = proof (T-empty (c λ _ x → x))

Type° : Type
Type° = Type

record Type' : Type where
  field
    fwd : Type
    bwd : Type°

open Type'

{-# NO_POSITIVITY_CHECK #-}
data μ (F : Type → Type) : Type where
  fix : F (μ F) → μ F

{-# TERMINATING #-}
rec : {F : Type → Type} → (∀ {A B} → (A → B) → F A → F B) → {A : Type} → (F A → A) → μ F → A
rec map f = loop
  where
    loop : _
    loop (fix x) = f (map loop x)

U : Type
U = μ λ _ → (A : Type) → A → A

U-empty : U → ♯ ⊥
U-empty = rec (λ _ x → x) λ f → {!f U (fix f)!}
