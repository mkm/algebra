{-# OPTIONS --cubical --prop #-}
module Hypersphere where

open import Path
open import Circle using (S¹; base; loop)

data S³ : Type where
  base : S³
  cube : ⟪ ⟪ base ⟫ ⟫ =⟦ _ ⊢ ⟪ base ⟫ =⟦ _ ⊢ base ≡ base ⟧= ⟪ base ⟫ ⟧= ⟪ ⟪ base ⟫ ⟫

data _⊔_ (A B : Type) : Type where
  lft : A → A ⊔ B
  rgt : B → A ⊔ B
  _∼_ : (a : A) (b : B) → lft a ≡ rgt b

encode : S³ → S¹ ⊔ S¹
encode base = lft base
encode (cube i j k) = {!f i j k!}
  where
    cb : (i j k : I) → S¹ ⊔ S¹
    cb i j k = (loop i ∼ loop j) k
    α : (i j : I) → cb i j i0 ≡ lft base
    α i j h = cb (~ h ∧ i) (~ h ∧ j) i0
    β : (i j : I) → cb i j i1 ≡ lft base
    β i j h = cb (~ h ∧ i) (~ h ∧ j) (~ h) 

decode : S¹ ⊔ S¹ → S³
decode (lft _) = base
decode (rgt _) = base
decode ((base ∼ _) _) = base
decode ((loop _ ∼ base) _) = base
decode ((loop i ∼ loop j) k) = cube i j k
