{-# OPTIONS --cubical-compatible #-}
module Prim.Core where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_; SSet; SSetω)
  renaming (Set to Type; Setω to Typeω)
  public

open import Agda.Builtin.Unit public
open import Agda.Builtin.Sigma public

data ⊥ : Type where

data Bool : Type where
  false true : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE true #-}

data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

postulate
  Char : Type
  String : Type
  Word64 : Type
  Float : Type

{-# BUILTIN CHAR Char #-}
{-# BUILTIN STRING String #-}
{-# BUILTIN WORD64 Word64 #-}
{-# BUILTIN FLOAT Float #-}

{-
infixr 20 _,_
record Σ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : A → Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

{-# BUILTIN SIGMA Σ #-}
-}

_×_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)
A × B = Σ A λ _ → B

infixr 10 _×_
