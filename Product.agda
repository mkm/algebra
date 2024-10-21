{-# OPTIONS --cubical --prop #-}
module Product where

open import Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Unit
open import String
open import Show

record _×_ (A B : Type) : Type where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

infixr 10 _×_

×-assoc-equiv : {A B C : Type} → (A × B) × C ≃ A × (B × C)
×-assoc-equiv {A} {B} {C} = isoToEquiv φ
  where
    φ : Iso ((A × B) × C) (A × (B × C))
    Iso.fun φ ((x , y) , z) = x , (y , z)
    Iso.inv φ (x , (y , z)) = (x , y) , z
    Iso.rightInv φ _ = id
    Iso.leftInv φ _ = id

×-assoc : (A B C : Type) → (A × B) × C ≡ A × (B × C)
×-assoc A B C i =
  Glue (A × (B × C))
    λ { (i = i0) → ((A × B) × C) ,, ×-assoc-equiv
      ; (i = i1) → (A × (B × C)) ,, idEquiv _ }

×-Unit-left-equiv : {A : Type} → Unit × A ≃ A
×-Unit-left-equiv {A} = isoToEquiv φ
  where
    φ : Iso (Unit × A) A
    Iso.fun φ (unit , x) = x
    Iso.inv φ x = unit , x
    Iso.rightInv φ _ = id
    Iso.leftInv φ _ = id

×-Unit-left : (A : Type) → Unit × A ≡ A
×-Unit-left A i =
  Glue A
    λ { (i = i0) → (Unit × A) ,, ×-Unit-left-equiv
      ; (i = i1) → A ,, idEquiv _ }

×-Unit-right-equiv : {A : Type} → A × Unit ≃ A
×-Unit-right-equiv {A} = isoToEquiv φ
  where
    φ : Iso (A × Unit) A
    Iso.fun φ (x , unit) = x
    Iso.inv φ x = x , unit
    Iso.leftInv φ _ = id
    Iso.rightInv φ _ = id

×-Unit-right : (A : Type) → A × Unit ≡ A
×-Unit-right A i =
  Glue A
    λ { (i = i0) → (A × Unit) ,, ×-Unit-right-equiv
      ; (i = i1) → A ,, idEquiv _ }

_∼_ : ∀ {A B} → A × B → A × B → Type
(x₁ , x₂) ∼ (y₁ , y₂) = (x₁ ≡ y₁) × (x₂ ≡ y₂)

encode : ∀ {A B} (x y : A × B) → x ≡ y → x ∼ y
encode (x₁ , x₂) (y₁ , y₂) p = (λ i → fst (p i)) , (λ i → snd (p i))

instance
  show-× : ∀ {A B} ⦃ _ : Show A ⦄ ⦃ _ : Show B ⦄ → Show (A × B)
  Show.show (show-× {B = _} ⦃ s₁ ⦄ ⦃ s₂ ⦄) (x , y) = "(" ⋯ show x ⋯ " , " ⋯ show y ⋯ ")"

  show-path-× : ∀ {A B} ⦃ _ : ShowPath A ⦄ ⦃ _ : ShowPath B ⦄ → ShowPath (A × B)
  Show.show show-path-× p =
    let p₁ , p₂ = encode _ _ p in "(" ⋯ show p₁ ⋯ " , " ⋯ show p₂ ⋯ ")"
